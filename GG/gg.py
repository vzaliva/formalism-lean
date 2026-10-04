"""A literal rendering in Python of Goodenough and Gerhart's corrected version
of Naur's program (Figure 3.3, p. 57 of the 1977 chapter, Figure 3, p. 496 of
the 1975 paper).

The program itself is `gg` below.  It keeps their variable names, their
one-based buffer, their order of statements, and the repeat ... until as a
loop with the same exit condition.  Nothing is added to it.  Differences of
notation only: BL and NL are the characters " " and "\\n", and ET is the
character "\\x03", which the harness refuses to accept in a text.

Everything from the line "Harness" on is not theirs: the feeding of the
characters, the single ET, the collection of output, and the mechanical
checks of their output properties O1-O4 (and O5, their oversize-word clause).

See gg-1977-corrected-program.txt beside this file for the transcription.
"""

import os
import sys

BL = " "
NL = "\n"
ET = "\x03"          # end-of-text character.  A dedicated control character,
                     # not a character a text can contain (run() checks this).


def gg(incharacter, outcharacter, MAXPOS):
    """Their program, statement for statement.  Returns the final Alarm.

    `incharacter()` returns the next input character.
    `outcharacter(c)` consumes one output character.
    """
    buffer = [None] * (MAXPOS + 1)       # one-based, as in the figure

    Alarm = False                        # Alarm := false;
    bufpos = 0                           # bufpos := 0;
    fill = 0                             # fill := 0;
    while True:                          # repeat
        CW = incharacter()               #   incharacter(CW);
        if CW == BL or CW == NL or CW == ET:     # if CW = BL v CW = NL v CW = ET
            # then begin
            if bufpos != 0:              #   if bufpos != 0
                # then begin
                if fill + bufpos < MAXPOS and fill != 0:   # if fill + bufpos < MAXPOS ^ fill != 0
                    # then begin
                    outcharacter(BL)     #     outcharacter(BL);
                    fill = fill + 1      #     fill := fill + 1 end
                else:                    #   else begin
                    outcharacter(NL)     #     outcharacter(NL);
                    fill = 0             #     fill := 0 end;
                for k in range(1, bufpos + 1):     # for k := 1 step 1 until bufpos do
                    outcharacter(buffer[k])        #   outcharacter(buffer[k]);
                fill = fill + bufpos     #   fill := fill + bufpos;
                bufpos = 0               #   bufpos := 0 end end
        else:                            # else
            if bufpos == MAXPOS:         #   if bufpos = MAXPOS
                Alarm = True             #   then Alarm := true
            else:                        #   else begin
                bufpos = bufpos + 1      #     bufpos := bufpos + 1;
                buffer[bufpos] = CW      #     buffer[bufpos] := CW end
        if Alarm or CW == ET:            # until Alarm v CW = ET;
            break
    return Alarm


# ---------------------------------------------------------------------------
# Harness.  Nothing below is theirs.
# ---------------------------------------------------------------------------

class ReadPastET(Exception):
    """Harness only: the program asked for a character after the ET."""


def run(text, MAXPOS):
    """Feed the characters of `text` followed by exactly one ET.

    Returns (output, alarm).  Raises ReadPastET if the program calls
    incharacter again after ET, which their loop never does.
    """
    assert ET not in text, "the sentinel ET must not occur in a text"
    chars = iter(text + ET)
    out = []

    def incharacter():
        try:
            return next(chars)
        except StopIteration:
            raise ReadPastET()

    alarm = gg(incharacter, out.append, MAXPOS)
    return "".join(out), alarm


def show(s):
    """Make blanks and new lines visible."""
    return s.replace(" ", "␣").replace("\n", "↵\n")


# Naur's own text and his two printed illustrations are imported, not copied,
# from the sibling exhibit, so there is one copy of them.  Bytecode writing is
# switched off so that the import leaves no __pycache__ in Naur/.
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "Naur"))
from naur import NAUR_TEXT, NAUR_15, NAUR_25     # noqa: E402


def is_break(c):
    return c == BL or c == NL


def words(s):
    return s.replace(NL, BL).split()


def check(text, MAXPOS, out, alarm):
    """Their output properties, checked mechanically.  Returns {name: bool}.

    O1  a new line occurs only at the very start of the output or between two
        words (the characters on both sides are nonbreak characters).
    O2  no two adjacent break characters in the output.
    O3  greedy filling: the first word of each line after the first would not
        have fitted on the line before (that line, a blank, the word).  An
        empty line before the end of the output fails this.
    O4  no line longer than MAXPOS.
    O5  Alarm is true exactly when some word of the text is longer than MAXPOS
        (their oversize-word clause).
    W   not theirs: the words written are the words of the text, in order, and
        all of them unless Alarm.  (On Alarm, the words written are a prefix.)
    """
    r = {}
    r["O1"] = all(i == 0 or (0 < i < len(out) - 1
                             and not is_break(out[i - 1]) and not is_break(out[i + 1]))
                  for i, c in enumerate(out) if c == NL)
    r["O2"] = not any(is_break(a) and is_break(b) for a, b in zip(out, out[1:]))
    lines = out.split(NL)
    if out.startswith(NL):
        lines = lines[1:]                 # the permitted new line at the start
    ok3 = True
    for prev, cur in zip(lines, lines[1:]):
        w = cur.lstrip(BL).split(BL)[0]
        if w == "" or len(prev) + 1 + len(w) <= MAXPOS:
            ok3 = False
    if out and lines and lines[-1] == "" and len(lines) > 1:
        ok3 = False                       # trailing empty line
    r["O3"] = ok3
    r["O4"] = all(len(l) <= MAXPOS for l in lines)
    r["O5"] = alarm == any(len(w) > MAXPOS for w in words(text))
    ws_in, ws_out = words(text), words(out)
    r["W"] = ws_out == ws_in if not alarm else ws_out == ws_in[:len(ws_out)]
    return r


def report(title, text, MAXPOS, expected=None):
    out, alarm = run(text, MAXPOS)
    print(f"=== {title}  (MAXPOS = {MAXPOS}, Alarm = {alarm})")
    print(f"input:  {show(text)}")
    print("output:")
    print(show(out))
    if expected is not None:
        print("matches the printed illustration exactly:", out == expected)
        stripped = out[1:] if out.startswith(NL) else out
        print("matches after removing one leading new line:", stripped == expected)
    r = check(text, MAXPOS, out, alarm)
    print("  ".join(f"{k} {'pass' if v else 'FAIL'}" for k, v in r.items()))
    print()
    return r


if __name__ == "__main__":
    print("Naur's own text, fed as one line with no final separator")
    report("committee, bare", NAUR_TEXT, 15, NAUR_15)
    report("committee, bare", NAUR_TEXT, 25, NAUR_25)

    print("Naur's own text, fed with a final NL")
    report("committee + NL", NAUR_TEXT + NL, 15, NAUR_15)
    report("committee + NL", NAUR_TEXT + NL, 25, NAUR_25)

    print("One input per Naur error (G&G's corrections 1-7; N1-N7 in 1975)")
    report("1 end of text reached, last word written", "AB CD" + NL, 5)
    report("2 last word with no following break", "AB CD", 5)
    report("3 first word shorter than MAXPOS", "AB CD", 5)
    report("4 first word exactly MAXPOS long", "ABCDE FG", 5)
    report("5 two blanks between words", "AB  CD", 5)
    report("5 three blanks between words", "AB   CD", 5)
    report("5 two blanks, line nearly full", "ABCD  E", 5)
    report("5 blank then NL between words", "AB " + NL + "CD", 5)
    report("6 blank before the first word", " AB CD", 5)
    report("6 NL before the first word", NL + "AB CD", 5)
    report("7 NL inside the text", "AB" + NL + "CD", 5)

    print("Other inputs")
    report("empty input (ET only)", "", 5)
    report("blanks only", "   ", 5)
    report("a single NL", NL, 5)
    report("oversize word", "AB ABCDEF G", 5)
    report("oversize word first", "ABCDEF G", 5)
    report("last line exactly MAXPOS long (two words)", "AB CD", 5)
    report("last line exactly MAXPOS long (one word)", "AB CDEFG", 5)
    report("two words filling a line exactly", "A BCD EF", 5)
    report("WHO WHAT WHEN (Meyer 1985)", "WHO WHAT WHEN", 10)
