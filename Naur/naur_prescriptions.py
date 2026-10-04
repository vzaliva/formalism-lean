"""Naur's seven prescriptions, checked at run time against his program.

Naur collects them on pp. 256-257 "as an important part of the documentation"
and says (p. 257) that each "could be written in a General Snapshot anywhere
in the program except between two actions of a cluster".  So they are checked
here at every cluster boundary and at the top of the loop, through the
`trace` hook in naur.py.  Nothing in the program is changed.

The prescriptions, in his words:

  (1) The number of characters currently held in the buffer is given by bufpos.
  (2) None of the characters held in the buffer has been produced as output.
  (3) The buffer never holds a BLANK or a NL character.
  (4) The input character preceding the one held in buffer[1] was a BLANK or
      NL. This has not been output.
  (5) The number of characters output since the last NL (new line) is given
      by fill.
  (6) Between two successive NL characters in the output there will be at
      most MAXPOS other characters.
  (7) bufpos <= MAXPOS.

How each is read here, since a check has to decide what the words mean:

  (1) bufpos equals the number of characters put into the buffer by Cluster 2
      and not yet taken out by Cluster 3 (a shadow count kept by the checker).
  (2) No input character now in the buffer has been written.  Characters are
      tracked by input position, so this is about the instances, not the
      values.
  (3) As written.
  (4) When the buffer is not empty: the input character just before the one
      in buffer[1] exists, is BLANK or LF, and no output has yet been written
      on its behalf.  The program writes a BLANK or LF in Action 1 to stand
      for that separator, so after Cluster 5 or Cluster 4 and before Cluster 3
      it counts as output.
  (5) fill equals the number of output characters after the last LF written
      (or all of them, if none has been).
  (6) Every completed output line, between two LFs, has at most MAXPOS
      characters.  The open line is reported separately, since the words say
      "between two successive NL characters".
  (7) As written.

Run:  python3 Naur/naur_prescriptions.py
"""

import sys
sys.dont_write_bytecode = True
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from naur import naur, BLANK, LF, Alarm, EndOfText, NAUR_TEXT, show  # noqa: E402


def check(text, MAXPOS):
    """Run the program on `text` and return the list of violations.

    Each violation is (prescription number, point label, input position
    just read, explanation)."""
    chars = iter(text)
    inp = []                  # input characters read so far, by position
    out = []                  # output characters
    buffered = []             # input positions now in the buffer (shadow of (1), (2))
    written = set()           # input positions already written out
    sep_written = [False]     # the separator before buffer[1] has been stood for in output
    violations = []

    def incharacter():
        try:
            c = next(chars)
        except StopIteration:
            raise EndOfText()
        inp.append(c)
        return c

    def outcharacter(c):
        out.append(c)

    def trace(label, bufpos, fill, buf):
        # Keep the shadow state in step with the clusters.
        if label == "C2":
            buffered.append(len(inp) - 1)
        elif label in ("C5", "C4") and inp:        # Action 1 wrote the separator's stand-in
            sep_written[0] = True
        elif label == "C3":
            written.update(buffered)
            buffered.clear()
            sep_written[0] = False
        pos = len(inp) - 1

        def bad(n, why):
            violations.append((n, label, pos, why))

        # (1)
        if bufpos != len(buffered):
            bad(1, f"bufpos = {bufpos}, buffer holds {len(buffered)}")
        # (2)
        hit = [p for p in buffered if p in written]
        if hit:
            bad(2, f"buffered positions already output: {hit}")
        # (3)
        if any(c in (BLANK, LF) for c in buf):
            bad(3, f"buffer holds a separator: {show(''.join(buf))!r}")
        # (4)
        if bufpos >= 1:
            p = buffered[0] - 1
            if p < 0:
                bad(4, "no input character precedes buffer[1] (first word)")
            elif inp[p] not in (BLANK, LF):
                bad(4, f"character before buffer[1] is {inp[p]!r}, not a separator")
            elif sep_written[0]:
                bad(4, "the separator before buffer[1] has been output")
        # (5)
        if fill is not None:
            # characters after the last LF:
            since = len(out) - 1 - max(i for i, c in enumerate(out) if c == LF) if LF in out else len(out)
            if fill != since:
                bad(5, f"fill = {fill}, output since last LF = {since}")
        # (6)
        lines = "".join(out).split(LF)
        for i, line in enumerate(lines[:-1]):
            if len(line) > MAXPOS:
                bad(6, f"completed line {i} has {len(line)} > MAXPOS characters")
        if len(lines[-1]) > MAXPOS:
            bad(6, f"OPEN line has {len(lines[-1])} > MAXPOS characters (not a violation as worded)")
        # (7)
        if bufpos > MAXPOS:
            bad(7, f"bufpos = {bufpos} > MAXPOS")

    try:
        naur(incharacter, outcharacter, MAXPOS, trace=trace)
    except (EndOfText, Alarm):
        pass
    return violations


CASES = [
    ("committee + LF, 15", NAUR_TEXT + LF, 15),
    ("committee + LF, 25", NAUR_TEXT + LF, 25),
    ("committee bare, 25", NAUR_TEXT, 25),
    ("empty", "", 5),
    ("one word + LF", "ABC" + LF, 5),
    ("two words + LF", "AB CD" + LF, 5),
    ("two blanks between words", "AB  CD" + LF, 5),
    ("two blanks, line nearly full", "ABCD  E" + LF, 5),
    ("leading blank", " AB CD" + LF, 5),
    ("leading LF", LF + "AB CD" + LF, 5),
    ("blanks only", "   ", 5),
    ("first word exactly MAXPOS", "ABCDE FG" + LF, 5),
    ("oversize word", "ABCDEF G" + LF, 5),
    ("WHO WHAT WHEN, 10", "WHO WHAT WHEN" + LF, 10),
]

if __name__ == "__main__":
    from collections import defaultdict
    summary = defaultdict(set)      # prescription -> set of (point, kind)
    for title, text, m in CASES:
        v = check(text, m)
        print(f"=== {title}: {len(v)} violation(s)")
        seen = set()
        for n, label, pos, why in v:
            key = (n, label, why.split(" (")[0].split(":")[0])
            summary[n].add((label, why.split(",")[0]))
            if key in seen:
                continue            # one line per distinct kind per case
            seen.add(key)
            print(f"    ({n}) at {label:>3} after input position {pos:>3}: {why}")
    print()
    print("Summary over all cases:")
    for n in range(1, 8):
        if n in summary:
            kinds = sorted({(lab, why) for lab, why in summary[n]})
            print(f"  ({n}) FAILS at " + "; ".join(f"{lab}: {why}" for lab, why in kinds))
        else:
            print(f"  ({n}) holds at every check point")
