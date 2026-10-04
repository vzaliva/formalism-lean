"""A literal rendering in Python of Naur's final program (BIT 9(3), 1969, p. 256).

The program itself is `naur` below.  It keeps Naur's variable names, his
one-based buffer, his order of statements and his control flow, with the
`go to next character` rendered as an endless loop.  Three things are not
Naur's and are marked where they occur:

  * `Alarm` is undefined in the paper.  Here it raises `Alarm`.
  * The paper has no case for the end of the input text: `incharacter` is
    called for ever.  Here `incharacter` raises `EndOfText` when the input is
    exhausted, and `run` catches it.  Without this the rendering could not be
    run at all.  It is the harness stopping the program, not the program
    stopping.
  * Naur's final program writes LF where the prose of the paper says NL.  The
    rendering follows the program and calls it LF.

See naur-1969-final-program.txt beside this file for the transcription.
"""

BLANK = " "
LF = "\n"


class Alarm(Exception):
    """Naur's undefined `Alarm`: a character arrived for a full buffer."""


class EndOfText(Exception):
    """Not Naur's.  Raised by `incharacter` when the input is exhausted."""


def naur(incharacter, outcharacter, MAXPOS, trace=None):
    """Naur's program, statement for statement.

    `incharacter()` returns the next input character or raises `EndOfText`.
    `outcharacter(c)` consumes one output character.

    `trace`, if given, is not Naur's.  It is called at the points where he
    says his prescriptions hold, "anywhere in the program except between two
    actions of a cluster": after each cluster, and at the top of the loop.
    It receives a label, bufpos, fill (None before fill is first assigned)
    and the buffer's current contents.  naur_prescriptions.py uses it.
    """
    buffer = [None] * (MAXPOS + 1)       # integer array buffer[1: some upper limit]
    t = (lambda label, bufpos, fill: trace(label, bufpos, fill, buffer[1:bufpos + 1])) \
        if trace else (lambda *_: None)  # hook, not Naur's

    bufpos = 0                           # bufpos := 0;
    t("C1", bufpos, None)                # hook
    outcharacter(LF)                     # outcharacter(channel, LF); fill := 0;
    fill = 0
    t("C4", bufpos, fill)                # hook

    while True:                          # next character:
        t("top", bufpos, fill)           # hook
        cw = incharacter()               #   incharacter(channel, cw);
        if cw == BLANK or cw == LF:      #   if cw = BLANK v cw = LF then
            if fill + 1 + bufpos <= MAXPOS:   # begin if fill+1+bufpos <= MAXPOS then
                outcharacter(BLANK)      #     begin outcharacter(channel, BLANK); fill := fill+1 end
                fill = fill + 1
                t("C5", bufpos, fill)    # hook
            else:                        #     else
                outcharacter(LF)         #     begin outcharacter(channel, LF); fill := 0 end;
                fill = 0
                t("C4", bufpos, fill)    # hook
            for k in range(1, bufpos + 1):    # for k := 1 step 1 until bufpos do
                outcharacter(buffer[k])  #       outcharacter(channel, buffer[k]);
            fill = fill + bufpos         #     fill := fill+bufpos; bufpos := 0;
            bufpos = 0                   #   end
            t("C3", bufpos, fill)        # hook
        else:                            #   else
            if bufpos == MAXPOS:         #   if bufpos = MAXPOS then Alarm else
                raise Alarm()
            else:
                bufpos = bufpos + 1      #   begin bufpos := bufpos+1; buffer[bufpos] := cw end;
                buffer[bufpos] = cw
                t("C2", bufpos, fill)    # hook
        # go to next character;


# ---------------------------------------------------------------------------
# Harness.  Nothing below is Naur's.
# ---------------------------------------------------------------------------

def run(text, MAXPOS):
    """Run Naur's program on `text`.

    Returns (output, how_it_stopped), where how_it_stopped is "end of text"
    (the harness ran out of input to feed `incharacter`) or "Alarm".
    """
    chars = iter(text)
    out = []

    def incharacter():
        try:
            return next(chars)
        except StopIteration:
            raise EndOfText()

    try:
        naur(incharacter, out.append, MAXPOS)
    except EndOfText:
        return "".join(out), "end of text"
    except Alarm:
        return "".join(out), "Alarm"


def show(s):
    """Make blanks and line feeds visible."""
    return s.replace(" ", "␣").replace("\n", "↵\n")


NAUR_TEXT = ("A committee is a group of people unwilling to work, organised by "
             "other people incapable of doing so, to do work which is probably "
             "useless.")

# The two illustrations on p. 251, as printed.
NAUR_15 = """A committee is
a group of
people
unwilling to
work, organised
by other people
incapable of
doing so, to do
work which is
probably
useless."""

NAUR_25 = """A committee is a group of
people unwilling to work,
organised by other people
incapable of doing so, to
do work which is probably
useless."""


def report(title, text, MAXPOS, expected=None):
    out, stop = run(text, MAXPOS)
    print(f"=== {title}  (MAXPOS = {MAXPOS}, stopped: {stop})")
    print(f"input:  {show(text)!s}")
    print("output:")
    print(show(out))
    if expected is not None:
        print("matches the printed illustration exactly:", out == expected)
        # Also compare after discarding what G&G list as N3/N4 artefacts:
        # the leading LF and a leading BLANK on the first line.
        stripped = out.lstrip(LF)
        if stripped.startswith(BLANK):
            stripped = stripped[1:]
        print("matches after removing the leading LF and BLANK:", stripped == expected)
    print()


if __name__ == "__main__":
    print("Naur's own text, fed as one line with no final separator")
    report("committee, bare", NAUR_TEXT, 15, NAUR_15)
    report("committee, bare", NAUR_TEXT, 25, NAUR_25)

    print("Naur's own text, fed with a final NL")
    report("committee + LF", NAUR_TEXT + LF, 15, NAUR_15)
    report("committee + LF", NAUR_TEXT + LF, 25, NAUR_25)

    print("Problematic inputs")
    report("empty input", "", 5)
    report("one word, no separator", "ABC", 5)
    report("one word + LF", "ABC" + LF, 5)
    report("two blanks between words", "AB  CD" + LF, 5)
    report("three blanks between words", "AB   CD" + LF, 5)
    report("two blanks, line nearly full", "ABCD  E" + LF, 5)
    report("leading blank", " AB CD" + LF, 5)
    report("blanks only", "   ", 5)
    report("LF only", LF, 5)
    report("NL inside the text", "AB" + LF + "CD" + LF, 5)
    report("two NLs in a row", "AB" + LF + LF + "CD" + LF, 5)
    report("first word exactly MAXPOS long", "ABCDE FG" + LF, 5)
    report("oversize word", "ABCDEF G" + LF, 5)
    report("WHO WHAT WHEN (Meyer 1985)", "WHO WHAT WHEN" + LF, 10)
