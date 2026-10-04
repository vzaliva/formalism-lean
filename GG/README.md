# Goodenough and Gerhart's corrected program

A historical exhibit, not part of the Lean development and not an
implementation of any specification in this repository. It checks
Goodenough and Gerhart's corrected version of Naur's line-editing program
against their own specification and their own list of Naur's seven errors. It
sits beside `Naur/`, which does the same for Naur's original.

| File | Contents |
|---|---|
| `gg-1977-corrected-program.txt` | the 27-line program, Figure 3.3 on p. 57 of the 1977 chapter "Toward a Theory of Testing: Data Selection Criteria", transcribed from the page image. Line numbers and underlining are dropped. Provenance, notation and the 1975 differences are in the header |
| `gg.py` | a literal Python rendering, statement for statement, with a harness that feeds it a string and one `ET`, and checks the output against their properties O1-O4 |

Run `python3 GG/gg.py`. It imports `NAUR_TEXT`, `NAUR_15` and `NAUR_25` from
`Naur/naur.py` rather than copying them, with bytecode writing switched off so
that nothing is written into `Naur/`. Nothing else is imported and nothing is
written.

## The two editions

The program first appeared as Figure 3 on p. 496 of the 1975 paper (IEEE TSE
SE-1(2)), with the corrections to N1-N7 on p. 497, and again as Figure 3.3 in
the 1977 chapter. Compared line for line, the two figures have the same
statements, conditions and constants. They differ in begin/end punctuation
only. In 1975 line 7 is `then` with no `begin`, and line 20 has one `end`
where 1977 has two. Read literally, the `else` of line 21 in the 1975 figure
would then attach to `if bufpos != 0` rather than to the test on line 6. Line
23 in 1975 also has a semicolon between `Alarm := true` and `else`. The 1977
figure has matching brackets and is the one transcribed and run.

## What is rendered, and what is not

`ET` is the character `\x03`, chosen because `run` refuses a text containing
it. `run(text, MAXPOS)` feeds the characters of `text` and then exactly one
`ET`, and raises if the program asks for another character. No run does.
`BL` and `NL` are `" "` and `"\n"`. `gg` returns the final `Alarm`. The
properties O1-O4 are those on p. 56 of the 1977 chapter (1-4 there, O1-O4 in
1975), and they are checked as follows.

- O1: a new line is at the very start of the output, or has a nonbreak
  character on both sides.
- O2: no two adjacent break characters in the output.
- O3: the first word of each line after the first would not have fitted on the
  line before (that line, a blank, the word). An empty line fails it.
- O4: no line longer than `MAXPOS`.

Two further checks are the harness's own, not theirs. O5 is their oversize
clause (`Alarm` is true exactly when some word is longer than `MAXPOS`). W
requires that the words written are the words of the text in order, all of
them unless `Alarm`.

## What the run shows

**Leading new line.** The program writes a new line before the first word on
every input that has a word. Line 10 sends the first word down the `else`
branch, because `fill != 0` is false, so `outcharacter(NL)` is executed with
nothing before it. Their property 1 permits it ("a new line should start only
between words and at the beginning of the output text, if any") and so does the
1975 wording of O1 ("at the beginning of the output text, if any"). Their
correction 4 says "only one NL character will precede the first word of the
output text", which is what is observed. The output is empty for an empty text
and for a text of breaks only, so there the new line is not written. It is
also not written for a first word that is oversize.

**Naur's illustrations.** Naur's text at `MAXPOS = 15` and `25` gives exactly
`NAUR_15` and `NAUR_25` once the one leading new line is removed, and not
before. The result is the same with and without a final new line in the input.
(Naur's own program does not reproduce the `MAXPOS = 25` illustration; see
`Naur/README.md`.)

**The seven corrections, on these inputs (`MAXPOS = 5` unless stated).**

| Error | Input | Observed |
|---|---|---|
| 1 end of text | `AB CD` + NL | stops, no read past `ET` |
| 2 last word, no break | `AB CD` | `CD` is written |
| 3 leading blank | `AB CD` | `AB CD` after the new line, no blank |
| 4 first word exactly `MAXPOS` | `ABCDE FG` | `ABCDE`, then `FG`, no empty line |
| 5 repeated breaks | `AB  CD`, `AB   CD`, `ABCD  E`, `AB ` NL `CD` | one blank between words, none trailing or leading, a break falls cleanly |
| 6 break before first word | blank, then separately NL, before `AB CD` | no extra blank or line |
| 7 NL inside the text | `AB` NL `CD` | treated as a break, output `AB CD` |

O1-O5 and W pass on every one of the 24 outputs printed, including the two
Naur texts at both widths, each with and without a final new line, empty
input, blanks only, a single new line, a text whose last line is exactly
`MAXPOS` long, and `WHO WHAT WHEN` at `MAXPOS = 10` (output `WHO WHAT`, `WHEN`).
No case was found where an output fails one of O1-O4. The checker was also
run on hand-made bad outputs (a double leading new line, a doubled blank, a
short line before a word that would fit) and fails them.

**Oversize words.** For `AB ABCDEF G` at `MAXPOS = 5`, `Alarm` is true and the
output is the new line and `AB`. The oversize word is not written, and the
`G` after it is never read, since the loop exits on `Alarm`. The statement
says only that output up to the point of an error has the four properties,
which holds.

**Surprises.** Two were observed. The `MAXPOS = 25` illustration is reproduced
here though not by Naur's program, and the 1975 and 1977 figures differ in
their brackets although the prose around them is the same.

Passing these inputs says nothing about the program on others. These are
spot checks, not a proof.
