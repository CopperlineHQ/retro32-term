/*
 * Retro32 Terminal - speed test
 *
 * The test outputs either the contents of PROGDIR:speedtest.ans or, if the file cannot be opened,
 * 200 colored ASCII lines. The elapsed time is measured with CurrentTime().
 *
 * Build with m68k-amigaos-gcc / bebbo toolchain:
 *   m68k-amigaos-gcc -O3 -noixemul -o test-speed test-speed.c
 *
 * with VBCC optimization enabled:
 *   vc +aos68k -O3 -speed -o test-speed test-speed.c
 */


//#ifdef __GNUC__
/* Self-contained SDK slice (see the header for why): no NDK headers are
 * required beyond the toolchain's own <inline/macros.h>. */
//#include "amiga-mini.h"
//#else
/* Standard NDK headers */
#include <proto/exec.h>
#include <proto/dos.h>
#include <proto/graphics.h>
#include <proto/intuition.h>
#include <proto/console.h>
#include <devices/conunit.h>
//#endif

/* This terminal engine code is intentionally kept in the main compilation
 * unit to maximize compiler optimization opportunities, as byte-oriented
 * parsing generates a large number of small function calls.
 *
 * Outgoing data is routed through the caller-defined send_data() function,
 * allowing the terminal engine to output data through either serial or TCP
 * transports.
 */
static void ser_write(const UBYTE *data, LONG len);
#define send_data(data, len) ser_write((data), (len))
#include "term-engine.c"

/* Opened in library mode (CONU_LIBRARY) purely for RawKeyConvert. */
#ifdef AMIGA_MINI_H
struct Library *ConsoleDevice;
#else
struct Device *ConsoleDevice;
#endif

#ifdef AMIGA_MINI_H
struct Library *IntuitionBase;
struct Library *GfxBase;
#else
struct IntuitionBase *IntuitionBase;
struct GfxBase *GfxBase;
#endif

/* libnix provides stdio over the shell console; declared by hand because
 * this build deliberately uses no libc headers. */
extern int printf(const char *fmt, ...);

/* The 16-colour CGA/VGA text palette in ANSI order (pen = SGR colour
 * for 30-37, plus 8 for the bright half): black, red, green, yellow,
 * blue, magenta, cyan, white, then their bright forms. Pen 3 is CGA
 * brown, pen 8 the dark grey this palette exists for. Values are
 * 12-bit 0x0RGB, one nibble per gun. */
static const UWORD ansi_rgb4[16] = {
    0x0000, 0x0A00, 0x00A0, 0x0A50, 0x000A, 0x0A0A, 0x00AA, 0x0AAA,
    0x0555, 0x0F55, 0x05F5, 0x0FF5, 0x055F, 0x0F5F, 0x05FF, 0x0FFF,
};

static struct Screen *screen;
static struct Window *window;

/* Blank pointer sprite: control words + one bitplane row + terminator,
 * all zero. Must live in chip RAM and stay allocated while set. */
#define BLANK_POINTER_BYTES 12
static UWORD *blank_pointer;

static void ser_write(const UBYTE *data, LONG len)
{
    LONG i;
    for (i = 0; i < len; i++)
        term_feed(data[i]); // Local echo
}

/* Keystroke, translated: forward it down the line. RawKeyConvert emits
 * 8-bit CSI (0x9B) for special keys; BBSes expect the 7-bit ESC [ form,
 * so rewrite that one byte and pass everything else verbatim. */
static void forward_key(UBYTE c)
{
    static const UBYTE esc_bracket[2] = { 0x1B, '[' };
    if (c == 0x9B)
        ser_write(esc_bracket, 2);
    else
        ser_write(&c, 1);
}

/* Rawkey down-event to bytes on the wire, shared by both keyboard
 * paths (IDCMP on Kickstart, the CIA poll in the AROS kiosk). */
static void key_convert(UWORD code, UWORD qual)
{
    struct InputEvent ie;
    UBYTE buf[16];
    LONG n, i;

    ie.ie_NextEvent = NULL;
    ie.ie_Class = IECLASS_RAWKEY;
    ie.ie_SubClass = 0;
    ie.ie_Code = code;
    ie.ie_Qualifier = qual;
    ie.ie_EventAddress = 0;
#ifdef AMIGA_MINI_H
    ie.ie_Seconds = 0;
    ie.ie_Micros = 0;
#else
    ie.ie_TimeStamp.tv_secs = 0;
    ie.ie_TimeStamp.tv_micro = 0;
#endif
    n = RawKeyConvert(&ie, buf, (LONG)sizeof(buf), NULL);
    for (i = 0; i < n; i++)
        forward_key(buf[i]);
}

/* Kickstart keyboard input: RAWKEY IDCMP messages from our window,
 * translated through the same keymap path as the kiosk. input.device
 * stays alive on Kickstart, so key repeat works here. */
static void handle_idcmp(void)
{
    struct IntuiMessage *im;
#ifdef AMIGA_MINI_H
    while ((im = (struct IntuiMessage *)GetMsg(WINDOW_USERPORT(window)))) {
#else
    while ((im = (struct IntuiMessage *)GetMsg(window->UserPort))) {
#endif
        ULONG cls = im->Class;
        UWORD code = im->Code, qual = im->Qualifier;
        ReplyMsg(&im->ExecMessage);
        if (cls == IDCMP_RAWKEY && !(code & IECODE_UP_PREFIX))
            key_convert(code, qual);
    }
}

/* Pins the 8x8 Topaz everywhere it matters: the screen's own font (a
 * bare-floppy Kickstart boot can default to a wider Topaz; observed
 * 10x9 on 3.1) and the OpenFont in setup that the glyph extraction
 * reads. BBS pages are drawn for 80 columns of this face. */
static struct TextAttr topaz8 = { "topaz.font", 8, 0, 0 };

/* Exec's CreateMsgPort/CreateIORequest are V36+ and this program
 * otherwise runs on Kickstart 1.3, so the port and request are static
 * structures initialized by hand. The port is private (never
 * AddPort'ed), which is all CreateMsgPort produced here anyway; the
 * signal bit is the only real allocation. */
static struct MsgPort port_con;
static struct IOStdReq ioreq_con;
static struct MsgPort *con_port;
static struct IOStdReq *con_req;
static BOOL con_open;

static struct MsgPort *port_init(struct MsgPort *port)
{
    BYTE sig = AllocSignal(-1);
    if (sig < 0)
        return NULL;
    port->mp_Node.ln_Type = NT_MSGPORT;
    port->mp_Flags = PA_SIGNAL;
    port->mp_SigBit = (UBYTE)sig;
    port->mp_SigTask = FindTask(NULL);
    port->mp_MsgList.lh_Head = (struct Node *)&port->mp_MsgList.lh_Tail;
    port->mp_MsgList.lh_Tail = NULL;
    port->mp_MsgList.lh_TailPred = (struct Node *)&port->mp_MsgList.lh_Head;
    return port;
}

static struct IOStdReq *ioreq_init(struct IOStdReq *req, struct MsgPort *port)
{
    req->io_Message.mn_Node.ln_Type = NT_MESSAGE;
    req->io_Message.mn_ReplyPort = port;
    req->io_Message.mn_Length = sizeof(struct IOStdReq);
    return req;
}

static int setup(void)
{
    struct ColorSpec colors[17];
    struct TagItem screen_tags[3];
    struct NewScreen ns;
    struct NewWindow nw;
    struct TextFont *tf;
    WORD height, i;
    BOOL v36;

    /* 33 is Kickstart 1.2's version; every V36-only call below branches
     * on the version actually present. */
#ifdef AMIGA_MINI_H
    IntuitionBase = OpenLibrary("intuition.library", 33);
#else
    IntuitionBase = (struct IntuitionBase*) OpenLibrary("intuition.library", 33);
#endif
    if (!IntuitionBase)
        return 1;
#ifdef AMIGA_MINI_H
    GfxBase = OpenLibrary("graphics.library", 33);
#else
    GfxBase = (struct GfxBase*) OpenLibrary("graphics.library", 33);
#endif
    if (!GfxBase)
        return 2;
#ifdef AMIGA_MINI_H
    v36 = IntuitionBase->lib_Version >= 36;
#else
    v36 = IntuitionBase->LibNode.lib_Version >= 36;
#endif

    /* Hand the ANSI palette to intuition itself with SA_Colors: OpenScreen
     * applies it as the last step of its own colour setup, which is the
     * only ordering that reliably beats the OS defaults everywhere. AROS
     * in particular loads its preference palette onto every new screen,
     * and a manual SetRGB4 afterwards did not stick there. */
    for (i = 0; i < 16; i++) {
        colors[i].ColorIndex = i;
        colors[i].Red = (ansi_rgb4[i] >> 8) & 0xF;
        colors[i].Green = (ansi_rgb4[i] >> 4) & 0xF;
        colors[i].Blue = ansi_rgb4[i] & 0xF;
    }
    colors[16].ColorIndex = -1;
    colors[16].Red = colors[16].Green = colors[16].Blue = 0;

    screen_tags[0].ti_Tag = SA_Colors;
    screen_tags[0].ti_Data = (ULONG)colors;
    /* Keep the screen's title bar behind our backdrop window (it would
     * otherwise draw over the top text rows). */
    screen_tags[1].ti_Tag = SA_ShowTitle;
    screen_tags[1].ti_Data = FALSE;
    screen_tags[2].ti_Tag = TAG_DONE;
    screen_tags[2].ti_Data = 0;

    /* The geometry stays in the NewScreen (ViewModes selects hires; a
     * tags-only open picks the default monitor's lores and shows half the
     * columns), with the tags layered on top -- the classic ExtNewScreen
     * pattern -- when intuition is new enough to take tags at all. Four
     * bitplanes for the 16 ANSI colours: hires allows exactly 4 planes
     * on OCS/ECS, so this needs no AGA anywhere -- but the 80 KiB
     * bitmap must be chip RAM (bitplane DMA cannot reach the $C00000
     * trapdoor slow RAM), and an AROS boot in tight configs does not
     * leave that much chip free; there is deliberately no shallower
     * fallback, the terminal fails with a message instead of degrading
     * the palette. PAL rows first, NTSC rows if the machine cannot do
     * 256. */
    for (i = 0; i < (WORD)sizeof(ns); i++)
        ((UBYTE *)&ns)[i] = 0;
    ns.Width = 640;
    ns.Depth = 4;
    ns.DetailPen = 0;
    ns.BlockPen = 1;
    ns.ViewModes = HIRES;
    ns.Type = CUSTOMSCREEN | SCREENQUIET;
    ns.Font = (APTR)&topaz8;
    height = 256;
    ns.Height = height;
    screen = v36 ? OpenScreenTagList(&ns, screen_tags) : OpenScreen(&ns);
    if (!screen) {
        height = 200;
        ns.Height = height;
        screen = v36 ? OpenScreenTagList(&ns, screen_tags) : OpenScreen(&ns);
    }
    if (!screen)
        return 3;

    for (i = 0; i < (WORD)sizeof(nw); i++)
        ((UBYTE *)&nw)[i] = 0;
    nw.Width = 640;
    nw.Height = height;
    nw.IDCMPFlags = IDCMP_RAWKEY; /* the Kickstart keyboard path */
    nw.Flags = WFLG_SIMPLE_REFRESH | WFLG_BACKDROP | WFLG_BORDERLESS
        | WFLG_ACTIVATE | WFLG_RMBTRAP;
    nw.Screen = screen;
    nw.Type = CUSTOMSCREEN;
    window = OpenWindow(&nw);
    if (!window)
        return 4;

    /* A V34 intuition ignored the tags, so do their work by hand: drop
     * the title bar behind the backdrop window and load the palette.
     * The OpenScreen-applies-it ordering that SA_Colors exists for
     * only matters on AROS, which is always V36+; on Kickstart a
     * LoadRGB4 after the fact sticks. */
    if (!v36) {
        ShowTitle(screen, FALSE);
        LoadRGB4(ViewPortAddress(window), ansi_rgb4, 16);
    }

    /* The kiosk takes no pointer input, so hide the Intuition pointer:
     * a blank 1-row sprite (chip RAM, zeroed) instead of the busy/arrow
     * imagery darting over the text whenever the host mouse moves.
     * Failing to allocate just leaves the normal pointer - cosmetic. */
    blank_pointer = AllocMem(BLANK_POINTER_BYTES, MEMF_CHIP | MEMF_CLEAR);
    if (blank_pointer)
        SetPointer(window, blank_pointer, 1, 16, 0, 0);

    /* The engine's glyphs: the machine's own ROM Topaz 8. */
    tf = OpenFont(&topaz8);
    if (!tf)
        return 5;

    i = term_init(screen, tf);
    CloseFont(tf);
    if (i)
        return 6;

    /* console.device in library mode: no window, no unit task, just
     * the RawKeyConvert vector both keyboard paths translate with. */
    con_port = port_init(&port_con);
    if (!con_port)
        return 7;
    con_req = ioreq_init(&ioreq_con, con_port);
    if (OpenDevice("console.device", CONU_LIBRARY,
                   (struct IORequest *)con_req, 0))
        return 8;
    con_open = TRUE;
#ifdef AMIGA_MINI_H
    ConsoleDevice = (struct Library *)con_req->io_Device;
#else
    ConsoleDevice = con_req->io_Device;
#endif

    return 0;
}

static void cleanup(void)
{
    if (con_open)
        CloseDevice((struct IORequest *)con_req);
    /* The port and request are static; only the port's signal bit
     * was allocated. */
    if (con_port)
        FreeSignal(con_port->mp_SigBit);
    if (blank_pointer) {
        if (window)
            ClearPointer(window);
        FreeMem(blank_pointer, BLANK_POINTER_BYTES);
        blank_pointer = NULL;
    }
    if (window)
        CloseWindow(window);
    if (screen)
        CloseScreen(screen);
#ifdef AMIGA_MINI_H
    if (GfxBase)
        CloseLibrary(GfxBase);
    if (IntuitionBase)
        CloseLibrary(IntuitionBase);
#else
    if (GfxBase)
        CloseLibrary((struct Library*) GfxBase);
    if (IntuitionBase)
        CloseLibrary((struct Library*) IntuitionBase);
#endif
}

#define ESC_STR  "\x1B"  // ASCII Escape character (decimal 27, octal 033) as a C string
UBYTE recvBuffer[4096];

#define LocalPrint(s) term_puts((s))

static inline void ConWrite(UBYTE *data, long len)
{
    while (len-- > 0)
        term_feed(*data++);
}

void LocalFmt(char *ctl, ...)
{
    static unsigned char buf[2048];
    RawDoFmt(ctl, (long *)(&ctl + 1), (void (*))"\x16\xc0\x4e\x75", buf);
    term_puts(buf);
}

/* Run a terminal output speed test and display the elapsed time.
 *
 * The test outputs either the contents of PROGDIR:speedtest.ans or, if the file cannot be opened,
 * 200 colored ASCII lines. The elapsed time is measured with CurrentTime().
 *
 * The terminal cursor is temporarily hidden during the test.
 *
 */
static void SpeedTest(void)
{
    ULONG before_s, before_micros;
    ULONG after_s, after_micros;
    ULONG elapsed_tenths;
    BPTR fh;

    cursor_hide();

    fh = Open("PROGDIR:speedtest.ans", MODE_OLDFILE);

    CurrentTime(&before_s, &before_micros);

    if (fh == 0) // File open error, so simply print ASCII lines
    {
        int i;
        int color;

        for (i = 1; i < 201; i++)
        {
            color = i % 8;  // cycle through ANSI colors 0-7
            LocalFmt(ESC_STR "[3%ldmLine %ld.\r\n", color, i);  // ESC[3Xm -> set foreground color
        }
    }
    else
    {
        LONG len;

        while ((len = Read(fh, recvBuffer, sizeof(recvBuffer))) > 0)
            ConWrite(recvBuffer, len);

        Close(fh);
    }

    CurrentTime(&after_s, &after_micros);

    // Convert the elapsed time to tenths of a second, rounding to the nearest tenth using integer
    // arithmetic.
    // CurrentTime() updates the time at most 60 times per second, so the sub-second value has a
    // maximum resolution of about 0.01667 s, which is sufficient for a tenth-of-a-second
    // measurement.
    if (after_micros >= before_micros)
    {
        elapsed_tenths = (after_s - before_s) * 10
                       + (after_micros - before_micros + 50000) / 100000;
    }
    else
    {
        elapsed_tenths = (after_s - before_s - 1) * 10
                       + (1000000 - before_micros + after_micros + 50000) / 100000;
    }

    LocalFmt(ESC_STR "[0m" ESC_STR "[255B\r\nDuration: %ld.%ld seconds\r\n",
             elapsed_tenths / 10,
             elapsed_tenths % 10);

    printf("Duration: %lu.%lu seconds\r\n",
             elapsed_tenths / 10,
             elapsed_tenths % 10);

    if (fh == 0)
    {
        if (elapsed_tenths == 0)
        {
            LocalPrint("Rating: Incredible\r\n");
        }
        else
        {
            // Round to the nearest integer using integer arithmetic.
            LONG lines_per_second = (2000 + elapsed_tenths / 2) / elapsed_tenths;

            STRPTR rating;

            if      (lines_per_second < 20) rating = "Poor";
            else if (lines_per_second < 30) rating = "Average";
            else if (lines_per_second < 50) rating = "Good";
            else                             rating = "Excellent";

            LocalFmt("Speed: %ld lines/second\r\nRating: %s\r\n", lines_per_second, rating);
        }
    }

    #ifdef _DEBUG
        LocalPrint("WARNING: Use an optimized release binary for representative results!\r\n");
    #endif

    // Restore cursor visibility after the test.
    cursor_show();
}

int main(void)
{
    {
        int rc = setup();
        if (rc) {
            if (rc == 3)
                printf("term: cannot open the 16-colour screen - the 80K\n"
                       "4-bitplane bitmap needs free CHIP RAM (slow/fast\n"
                       "RAM cannot hold bitplanes). Give the machine more\n"
                       "chip RAM (1M chip on an A500-class config).\n");
            else
                printf("term: setup failed (step %d)\n", rc);
            cleanup();
            return 20;
        }
    }

    SpeedTest();

    ULONG winsig = 1L << window->UserPort->mp_SigBit;

    /* Wait for an IDCMP event or Ctrl-C, yielding the CPU while idle. */
    ULONG sig = Wait(winsig | SIGBREAKF_CTRL_C);

    /* Process pending IDCMP messages before closing the window. */
    if(sig & winsig)
        handle_idcmp();

    cleanup();
    return 0;
}
