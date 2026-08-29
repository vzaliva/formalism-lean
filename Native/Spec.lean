import Meyer.Common

/-!
# A Lean-native specification of the text-formatting problem

A third specification of the problem Meyer specified twice, `Meyer.Paper` and
`Meyer.Book`, written to use what Lean already has rather than to transcribe a
text.  It is the same problem:

> Given a text consisting of words separated by BLANKS or by NL (new line)
> characters, convert it to a line-by-line form in accordance with the following
> rules: (1) line breaks must be made only where the given text has BLANK or NL;
> (2) each line is filled as far as possible, as long as (3) no line will contain
> more than MAXPOS characters.

Both of Meyer's specifications work on the text as a sequence of characters and
recover its structure from that sequence: the paper by taking a longest
subsequence with no two adjacent break characters, the book by taking a shortest
element of the closure of a rewriting relation, and both by measuring lines as
the longest run of characters containing no new line.  This one reads the
structure off once, with `words`, and never looks at a character again.  An
output is a *layout*, a list of lines each of which is a list of words, and the
specification says three things about it: the lines carry the words of the
input in order, no line is empty, and no line prints wider than `M`.  Among the
layouts, those with fewest lines are the solutions, and the output is the
printed form of one of them.

Nothing here is an implementation.  `Layout` is a property, `Goal` is a relation,
and the relation is not a function: `Native.Properties` shows an input with two
outputs, as both of Meyer's texts do for theirs.

The module has two parts.  The first is the specification.  The second states,
as definitions, the properties `N1` to `N4` an output of the specification is
expected to have, in the way the book states `T1` to `T8` of `S1`; they are
read off the output with `List.splitOn` and `words`, and say nothing about how
the output was arrived at.  `Native.Properties` proves that `Goal` has them,
and that together they characterise it.

## What is and is not Meyer's

`Text`, `blank`, `newline` and `IsBreak` are the vocabulary the two Meyer
transcriptions share, and are taken from `Meyer.Common` so that the three
specifications can be compared.  `words` is the book's definition, exercise
9-E.6, character for character: split at the separators and discard the empty
pieces.  Everything else is new.

Where the two Meyer specifications differ, over separators at the two ends of
the text, this one sides with the book: a leading or trailing break is not a
word and leaves no trace in the output.  `Native.Comparison` proves the
relation equal to the book's and, through `Meyer.Comparison`, different from
the paper's.

The definitions are `noncomputable` only because this toolchain's
`List.splitOnP` and `List.intercalate` are; the kernel reduces both, and
`Native.Properties` supplies a `Decidable` instance for `Goal` so that concrete
claims are settled by `decide`.
-/

namespace Native

open Meyer

noncomputable section

/-- A word: a non-empty run of characters none of which is a break. -/
abbrev Word := Text

/-- A line: the words printed on it, in order. -/
abbrev Line := List Word

/-- The words of a text, in order: split at the breaks and drop the empty pieces.
This is `Meyer.Book.words`. -/
def words (t : Text) : List Word :=
  (t.splitOnP (IsBreak ·)).filter (· ≠ [])

/-- A line is printed with one blank between consecutive words. -/
def renderLine (l : Line) : Text :=
  List.intercalate [blank] l

/-- A layout is printed with one new line between consecutive lines. -/
def render (ls : List Line) : Text :=
  List.intercalate [newline] (ls.map renderLine)

/-- `ls` lays the words `ws` out in lines of at most `M` characters. -/
structure Layout (M : ℕ) (ws : List Word) (ls : List Line) : Prop where
  /-- The lines carry exactly the words, in order. -/
  flatten : ls.flatten = ws
  /-- No line is empty. -/
  nonempty : [] ∉ ls
  /-- No line prints wider than `M`. -/
  fits : ∀ l ∈ ls, (renderLine l).length ≤ M

/-- **The specification.**  `o` is the printed form of a layout of the words of
`i` that has as few lines as any layout of them. -/
def Goal (M : ℕ) (i o : Text) : Prop :=
  ∃ ls, Layout M (words i) ls ∧
    (∀ ls', Layout M (words i) ls' → ls.length ≤ ls'.length) ∧ o = render ls

/-! ## Properties

What an output should look like, stated on the output alone.  Lines are read
back with `List.splitOn`, which reads the empty text as one empty line; hence the
proviso `o ≠ []` where a property is about the lines.  `N1` and `N2` are the
book's `T6` and more; `N3` is its `T3`, about a solution rather than a recast.
These three are properties of the printed shape of the output and say nothing
about the minimisation.  `N4` does: no text that is well formed in the sense of
`N1` to `N3` has fewer lines.  The list is complete -- `Native.goal_iff_properties`
proves that the four together characterise `Goal` -- which is what the book's
`T1` to `T8` are not.  The book's `T1`, on the length of the output, has no
entry here because it is a consequence of `N1` to `N3`; `Native.length_of_goal`
states it in its sharpest form. -/

/-- `N1`: every line of the output is non-empty and no wider than `M`. -/
def LinesFit (M : ℕ) (o : Text) : Prop :=
  o ≠ [] → ∀ l ∈ o.splitOn newline, l ≠ [] ∧ l.length ≤ M

/-- `N2`: on every line, one blank between consecutive words and none at either
end -- splitting a line at its blanks leaves no empty piece. -/
def SingleBlanks (o : Text) : Prop :=
  o ≠ [] → ∀ l ∈ o.splitOn newline, [] ∉ l.splitOn blank

/-- `N3`: the output has exactly the words of the input, in order. -/
def SameWords (i o : Text) : Prop :=
  words o = words i

/-- `N4`: no text that has the words of the input, one blank between words and
lines that fit has fewer lines than the output. -/
def FewestLines (M : ℕ) (i o : Text) : Prop :=
  ∀ o', LinesFit M o' → SingleBlanks o' → SameWords i o' →
    o.count newline ≤ o'.count newline

end

end Native
