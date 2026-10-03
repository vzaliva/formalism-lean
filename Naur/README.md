# Naur's 1969 program

A historical exhibit, not part of the Lean development and not an
implementation of any specification in this repository. It exists to check
Naur's own illustrations against Naur's own program.

| File | Contents |
|---|---|
| `naur-1969-final-program.txt` | the final program from p. 256 of "Programming by Action Clusters", transcribed from the page image in Naur's Algol 60 notation, with his boxes around the clusters dropped |
| `naur.py` | a literal Python rendering of it, statement for statement, with a harness that feeds it a string and stops it when the input runs out |

Run `python3 Naur/naur.py`. Nothing is imported and nothing is written.

## What the run shows

Fed his own text with a final new line, the program reproduces the
`MAXPOS = 15` illustration on p. 251 once two things are discarded: the new
line it writes before anything else, and the blank it writes before the first
word (Goodenough and Gerhart's N3). 

It does **not** reproduce the `MAXPOS = 25` illustration even then. The leading
blank takes one column of the first line, so `of` no longer fits on it, and
every break after that moves. The result is another six-line layout. It meets
rule 2 in the fewest-lines reading, and fails it in Goodenough and Gerhart's
reading, "as many words as possible on a line", since the first line holds five
words where six would fit. Which reading rule 2 intends is exactly what the
statement does not say.

Without the final new line the last word, `useless.`, is never written (N2).

On the inputs the statement does not speak to, the program:

- writes a new line and then waits for ever on empty input (N1);
- passes repeated blanks through unchanged, and when a break falls among
  them leaves the extras as trailing blanks on one line or a leading blank
  on the next (N5);
- turns a blank or new line before the first word into two blanks (N6);
- writes an empty line before a first word that is exactly `MAXPOS` long (N4);
- writes three blanks for an input of three blanks, and one blank for a
  single new line;
- stops with `Alarm` on an oversize word, having written only the initial
  new line.

Every one of Goodenough and Gerhart's seven errors is visible in the output,
N7 included, since the rendering follows the program in calling the new-line
character `LF` where the paper's prose says `NL`.
