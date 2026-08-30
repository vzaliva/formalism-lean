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

The module has two parts.  The first is the specification, `Goal`, by way of
layouts.  The second is the same specification again, `Optimal`, on the output
text alone: the properties `N1` to `N4` an output is expected to have, in the
way the book states `T1` to `T8` of `S1`, bundled into a structure that is
itself a specification.  `Native.Properties` proves the two the same relation.

## What is and is not Meyer's

`Text`, `blank`, `newline` and `IsBreak` are the vocabulary the two Meyer
transcriptions share, and are taken from `Meyer.Common` so that the three
specifications can be compared.  `words` is the book's definition, exercise
9-E.6, character for character: split at the separators and discard the empty
pieces.  Everything else is new.

Where the two Meyer specifications differ, over separators at the two ends of
the text, this one sides with the book: a leading or trailing break is not a
word and leaves no trace in the output.  `Native.Comparison` proves the
relation equal to the book's; that it then differs from the paper's is
`Meyer.Comparison`.

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

/-! ## The specification again, on texts

`Goal` says what an output is by way of a layout, a list of lines of words.
The same problem can be specified on the output text alone, with nothing behind
it.  An output is *acceptable* if its lines are non-empty and fit, its words are
separated by single blanks, and they are the words of the input; it is *optimal*
if no acceptable text has fewer lines.  The fields are the properties `N1` to
`N4`, each read off the output with `List.splitOn` and `words`; `List.splitOn`
reads the empty text as one empty line, hence the proviso `o ≠ []` in `N1` and
`N2`.

The two formulations are the same relation, `Native.goal_iff_optimal`, and
each has what the other lacks.  `Goal` is decidable and comes with an induction
on layouts.  `Optimal` is the problem statement as Naur posed it, read off the
output, and has the shape Meyer's specifications have -- a minimisation over a
set of candidates: it is `MIN_SET` of `Acceptable` under the number of new
lines, `Native.optimal_iff_minSet`, as the 1985 `goal` is `MIN_SET` of
`TRANSF (i)`.  The book's `T1` to `T8` have no counterpart to
`goal_iff_optimal`; that is the point of stating the properties as a
specification. -/

/-- `N1` to `N3`: what any acceptable output of `i` looks like. -/
structure Acceptable (M : ℕ) (i o : Text) : Prop where
  /-- `N1`: every line is non-empty and no wider than `M`. -/
  linesFit : o ≠ [] → ∀ l ∈ o.splitOn newline, l ≠ [] ∧ l.length ≤ M
  /-- `N2`: one blank between consecutive words on a line, none at either end --
  splitting a line at its blanks leaves no empty piece. -/
  singleBlanks : o ≠ [] → ∀ l ∈ o.splitOn newline, [] ∉ l.splitOn blank
  /-- `N3`: the words of the input, in order. -/
  sameWords : words o = words i

/-- `N1` to `N4`: an acceptable output with fewest lines among the acceptable
outputs.  **The specification, on texts.** -/
structure Optimal (M : ℕ) (i o : Text) : Prop extends Acceptable M i o where
  /-- `N4`: no acceptable output has fewer lines. -/
  fewestLines : ∀ o', Acceptable M i o' → o.count newline ≤ o'.count newline

end

end Native
