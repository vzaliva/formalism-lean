import Meyer.Paper.Check
import Meyer.Char

/-!
# The 1985 specification, decided

`Meyer.Paper.Check` makes `goal` decidable.  This module uses that at `Char`:
every claim below is settled by `decide`, and checked by the kernel, with no
proof by hand.

* Meyer's own example, `WHO WHAT WHEN` at `MAXPOS = 10`, which
  `Meyer.Paper.Examples` settles by hand.
* Naur's example sentence, 25 words and 138 characters, at `MAXPOS = 15` and
  `25`.  Each case takes a fraction of a second.
* Inputs with separators at the ends, where the 1985 and 2022 specifications part
  (`Meyer.Comparison`).

## Writing long texts

A long text is written below as its lines, each a list of words, joined by
`lines`.  The kernel decodes a string literal in time worse than linear in its
length: `String.toList` of Naur's sentence as one literal costs it about a second,
of the same sentence as 25 words almost nothing.  `lines` is checked against a
literal on a short text.
-/

namespace Meyer.Paper

/-- A text given by its lines, each a list of words: the words of a line joined
by a blank, the lines by a new line. -/
private def lines (ls : List (List String)) : Text Char :=
  List.intercalate [newline] (ls.map fun l => List.intercalate [blank] (l.map String.toList))

example : lines [["WHO", "WHAT"], ["WHEN"]] = "WHO WHAT\nWHEN".toList := by decide

/-! ## `WHO WHAT WHEN`

Meyer's example, with `MAXPOS = 10`: "there are two equally correct two-line
solutions (`WHAT` may be on either the first or second line)".  The three-line
one is not a solution. -/

example : Goal 10 "WHO WHAT WHEN".toList "WHO WHAT\nWHEN".toList ∧
    Goal 10 "WHO WHAT WHEN".toList "WHO\nWHAT WHEN".toList ∧
    ¬ Goal 10 "WHO WHAT WHEN".toList "WHO\nWHAT\nWHEN".toList := by
  decide

/-! ## Naur's sentence

Naur's own example text, as one line. -/

/-- "A committee is a group of people unwilling to work, organised by other people
incapable of doing so, to do work which is probably useless." -/
private def naur : Text Char := lines
  [["A", "committee", "is", "a", "group", "of", "people", "unwilling", "to", "work,", "organised",
    "by", "other", "people", "incapable", "of", "doing", "so,", "to", "do", "work", "which", "is",
    "probably", "useless."]]

example : naur.length = 138 := by decide +kernel

/-! ### `MAXPOS = 15`

Filled line by line, the sentence takes eleven lines, and no layout takes fewer.
The specification asks for fewest lines, not for each line to be filled before
the next is begun, so moving a word down is acceptable as long as the count
stays the same.  One more line is not acceptable, and one fewer is not possible:
the layout below that saves a line has a line of seventeen characters. -/

/-- Filled line by line. -/
private def naur15 : Text Char := lines
  [["A", "committee", "is"],
   ["a", "group", "of"],
   ["people"],
   ["unwilling", "to"],
   ["work,", "organised"],
   ["by", "other", "people"],
   ["incapable", "of"],
   ["doing", "so,", "to", "do"],
   ["work", "which", "is"],
   ["probably"],
   ["useless."]]

/-- `is` moved to the second line: not filled line by line, as few lines. -/
private def naur15Moved : Text Char := lines
  [["A", "committee"],
   ["is", "a", "group", "of"],
   ["people"],
   ["unwilling", "to"],
   ["work,", "organised"],
   ["by", "other", "people"],
   ["incapable", "of"],
   ["doing", "so,", "to", "do"],
   ["work", "which", "is"],
   ["probably"],
   ["useless."]]

/-- One line more: `is` on a line of its own. -/
private def naur15Longer : Text Char := lines
  [["A", "committee", "is"],
   ["a", "group", "of"],
   ["people"],
   ["unwilling", "to"],
   ["work,", "organised"],
   ["by", "other", "people"],
   ["incapable", "of"],
   ["doing", "so,", "to", "do"],
   ["work", "which"],
   ["is"],
   ["probably"],
   ["useless."]]

/-- One line fewer, by a line of seventeen characters. -/
private def naur15Wide : Text Char := lines
  [["A", "committee", "is"],
   ["a", "group", "of", "people"],
   ["unwilling", "to"],
   ["work,", "organised"],
   ["by", "other", "people"],
   ["incapable", "of"],
   ["doing", "so,", "to", "do"],
   ["work", "which", "is"],
   ["probably"],
   ["useless."]]

/-- The greedy fill is the layout filled line by line. -/
example : fill 15 (compact naur) = naur15 := by decide

example : Goal 15 naur naur15 := by decide

example : Goal 15 naur naur15Moved := by decide

example : ¬ Goal 15 naur naur15Longer := by decide

example : ¬ Goal 15 naur naur15Wide := by decide

/-! ### `MAXPOS = 25`

Six lines, the first five exactly twenty-five characters wide.  Moving
`probably` down to the last line keeps six, and is acceptable; putting `useless.`
on a line of its own as well makes seven, and is not. -/

/-- Filled line by line. -/
private def naur25 : Text Char := lines
  [["A", "committee", "is", "a", "group", "of"],
   ["people", "unwilling", "to", "work,"],
   ["organised", "by", "other", "people"],
   ["incapable", "of", "doing", "so,", "to"],
   ["do", "work", "which", "is", "probably"],
   ["useless."]]

/-- `probably` moved to the last line: not filled line by line, as few lines. -/
private def naur25Moved : Text Char := lines
  [["A", "committee", "is", "a", "group", "of"],
   ["people", "unwilling", "to", "work,"],
   ["organised", "by", "other", "people"],
   ["incapable", "of", "doing", "so,", "to"],
   ["do", "work", "which", "is"],
   ["probably", "useless."]]

/-- One line more. -/
private def naur25Longer : Text Char := lines
  [["A", "committee", "is", "a", "group", "of"],
   ["people", "unwilling", "to", "work,"],
   ["organised", "by", "other", "people"],
   ["incapable", "of", "doing", "so,", "to"],
   ["do", "work", "which", "is"],
   ["probably"],
   ["useless."]]

/-- The greedy fill is the layout filled line by line. -/
example : fill 25 (compact naur) = naur25 := by decide

example : Goal 25 naur naur25 := by decide

example : Goal 25 naur naur25Moved := by decide

example : ¬ Goal 25 naur naur25Longer := by decide

/-! ## Separators at the ends

Where the 1985 specification and the 2022 one part.  The 1985 one keeps one
break of every run, the runs at the two ends included, and the break it keeps
there may become a new line; the 2022 one deletes them (`T6`). -/

/-- A leading blank stays, on a line that has room for it. -/
example : Goal 10 " AB CD".toList " AB CD".toList ∧
    ¬ Goal 10 " AB CD".toList "AB CD".toList := by
  decide

/-- Separators only: one blank, if a line has room for one
(`goal_of_forall_isBreak`); never the empty text. -/
example : Goal 5 "   ".toList " ".toList ∧ ¬ Goal 5 "   ".toList "".toList := by
  decide

/-- At `MAXPOS = 0` the blank is a line too long, and becomes a new line. -/
example : Goal 0 "   ".toList "\n".toList ∧ ¬ Goal 0 "   ".toList " ".toList := by
  decide

/-- A leading blank on a line with no room for it becomes a new line: the output
begins with an empty line.  `Meyer.Comparison.Examples` proves the first two by
hand. -/
example : Goal 2 " AB".toList "\nAB".toList ∧ ¬ Goal 2 " AB".toList "AB".toList ∧
    ¬ Goal 2 " AB".toList " AB".toList := by
  decide

end Meyer.Paper
