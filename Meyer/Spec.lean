import Mathlib.Data.List.Chain
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Lattice

/-!
# Meyer's formal specification of the text-formatting problem

A transcription into Lean of the formal specification given in

> Bertrand Meyer, *On Formalism in Specifications*, IEEE Software 2(1):6-26,
> 1985.  DOI 10.1109/MS.1985.229776

of the text-formatting problem due to Naur, later criticised by Goodenough and
Gerhart:

> Given a text consisting of words separated by BLANKS or by NL (new line)
> characters, convert it to a line-by-line form in accordance with the following
> rules: (1) line breaks must be made only where the given text has BLANK or NL;
> (2) each line is filled as far as possible, as long as (3) no line will contain
> more than MAXPOS characters.

This module contains the **specification only**.  There is no implementation; the
intent is that it stands alone as a faithful rendering of Meyer's paper, against
which any other treatment of the problem can later be shown equivalent.

## Structure

Meyer builds the specification as a composition of two relations and a function:

```
short_breaks (r)  ->  limited_length (r)  ->  FEWEST_LINES (f)
```

and defines `goal (i, o)` to hold exactly when `o ∈ FEWEST_LINES (TRANSF (i))`.
The names below follow his, with `CamelCase` for `Set`- and `Prop`-valued
definitions as is usual in Lean.

## Deviations from the paper

* Meyer keeps `CHAR` abstract, noting that "the only property of CHAR that
  matters here is that CHAR contains two elements of particular interest,
  `blank` and `new_line`".  We instantiate it at `Char`, which costs nothing and
  makes the specification concrete.

* Meyer defines a subsequence of `s` as `s ∘ u` for `u` a *sorted* sequence of
  indices, where sorted means `u (i-1) ≤ u (i)`.  Taken literally the
  non-strict inequality permits an index to repeat, which would make
  `SINGLE_BREAKS` unbounded and `MAX_SET` undefined; strictly increasing is
  plainly intended, and that is exactly `List.Sublist`.  `Meyer.Bug` formalises
  the literal reading and proves it incompatible with his domain theorem.

* `MAX_SET` and `MIN_SET` are rendered as "no element of the set does better",
  which agrees with Meyer wherever the extremum exists and is simply empty
  otherwise.  Meyer instead requires finiteness as a side condition; he observes
  that it holds at the one place he needs it.
-/

namespace Meyer

/-! ## Characters and texts -/

/-- Meyer's `seq [CHAR]`, used for both `INPUT` and `OUTPUT`.  He notes that
describing the output as `seq [LINE]` was available and chose not to. -/
abbrev Text := List Char

/-- Meyer's `blank`. -/
def blank : Char := ' '

/-- Meyer's `new_line`. -/
def newline : Char := '\n'

/-- `BREAK_CHAR ≜ {blank, new_line}`. -/
def IsBreak (c : Char) : Prop := c = blank ∨ c = newline

instance : DecidablePred IsBreak :=
  fun c => inferInstanceAs (Decidable (c = blank ∨ c = newline))

/-! ## Extremal subsets

`MAX_SET (X, f)` and `MIN_SET (X, f)`.  Meyer stresses that these yield a
*subset* of `X` rather than a single element, "since there may be more than one
element with minimum or maximum `f` value" -- the source of the specification's
nondeterminism. -/

/-- `MAX_SET (X, f)`: the elements of `X` at which `f` attains its maximum. -/
def MaxSet {α : Type*} (X : Set α) (f : α → ℕ) : Set α :=
  {x ∈ X | ∀ y ∈ X, f y ≤ f x}

/-- `MIN_SET (X, f)`: the elements of `X` at which `f` attains its minimum. -/
def MinSet {α : Type*} (X : Set α) (f : α → ℕ) : Set α :=
  {x ∈ X | ∀ y ∈ X, f x ≤ f y}

/-! ## Short breaks

The first stage: runs of break characters in the input are compacted to a single
break, and every non-break character is retained. -/

/-- Meyer's condition on `SINGLE_BREAKS`, transcribed as he writes it:
`s (i-1) ∈ BREAK_CHAR → s (i) ∉ BREAK_CHAR`.  Equivalently, no two consecutive
characters are break characters. -/
def NoDoubleBreak (s : Text) : Prop :=
  s.IsChain fun x y => IsBreak x → ¬ IsBreak y

/-- `SINGLE_BREAKS (a)`: the subsequences of `a` in which no two consecutive
characters are break characters. -/
def SingleBreaks (a : Text) : Set Text :=
  {s | s.Sublist a ∧ NoDoubleBreak s}

/-- `COMPACTED (a) ≜ MAX_SET (SINGLE_BREAKS (a), length)`.

Meyer's remark on why this is the right definition: any `b ∈ COMPACTED (a)` must
have retained from `a` every non-break character -- had one been omitted it could
be reinserted to give a longer element of `SINGLE_BREAKS (a)` -- and has a single
break character wherever `a` had one or more consecutive ones. -/
def Compacted (a : Text) : Set Text :=
  MaxSet (SingleBreaks a) List.length

/-- `short_breaks (a, b) ≜ b ∈ COMPACTED (a)`: `a` and `b` are made of the same
sequence of words and breaks, but the breaks in `b` are single characters. -/
def ShortBreaks (a b : Text) : Prop :=
  b ∈ Compacted a

/-! ## Limited length

The second stage: break characters may be exchanged for one another, and the
result must have no line longer than `MAXPOS`. -/

/-- `EQUIVALENT (b)`: the sequences identical to `b` except that `new_line`
characters may be substituted for blanks or vice versa.  `List.Forall₂` forces
the two sequences to have the same length, which is the first of Meyer's two
conditions. -/
def Equivalent (b : Text) : Set Text :=
  {s | List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) s b}

/-- `max_line_length (s)`: "the maximum length of a line in `s`, expressed as the
maximum number of consecutive characters, none of which is a new line".

Note the asymmetry with `IsBreak`: only `newline` terminates a line, so blanks
count towards a line's length.  A stretch of consecutive characters is an infix,
and the set below is nonempty (it contains `0`, witnessed by `[]`) and bounded
above by `s.length`, so the supremum is the maximum Meyer intends. -/
noncomputable def maxLineLength (s : Text) : ℕ :=
  sSup {n | ∃ t : Text, t.IsInfix s ∧ newline ∉ t ∧ t.length = n}

/-- `number_of_new_lines (s) ≜ card {i | s (i) = new_line}`. -/
def numberOfNewLines (s : Text) : ℕ :=
  s.count newline

variable (MAXPOS : ℕ)

/-- `TRIMMED (b) ≜ {s ∈ EQUIVALENT (b) | max_line_length (s) ≤ MAXPOS}`. -/
def Trimmed (b : Text) : Set Text :=
  {s ∈ Equivalent b | maxLineLength s ≤ MAXPOS}

/-- `limited_length (b, c) ≜ c ∈ TRIMMED (b)`. -/
def LimitedLength (b c : Text) : Prop :=
  c ∈ Trimmed MAXPOS b

/-! ## Fewest lines, and the basic relation -/

/-- `FEWEST_LINES (SSC) ≜ MIN_SET (SSC, number_of_new_lines)`: those elements of
`SSC` having as few lines as possible. -/
def FewestLines (SSC : Set Text) : Set Text :=
  MinSet SSC numberOfNewLines

/-- `TRANSF (i) ≜ {s | tr (i, s)}` where `tr ≜ limited_length ∘ short_breaks`.
Meyer's `∘` is composition of relations, so this is the existential below. -/
def Transf (i : Text) : Set Text :=
  {s | ∃ b, ShortBreaks i b ∧ LimitedLength MAXPOS b s}

/-- **The basic relation.** `goal (i, o)` holds between input `i` and output `o`
iff `o ∈ FEWEST_LINES (TRANSF (i))`.

This is a relation and not a function: Meyer notes that "there may be more than
one correct output for a given input; in other words, a truly general
specification of the problem should be nondeterministic". -/
def Goal (i o : Text) : Prop :=
  o ∈ FewestLines (Transf MAXPOS i)

/-- `dom (goal)`, the inputs for which an acceptable output exists. -/
def DomGoal : Set Text :=
  {i | ∃ o, Goal MAXPOS i o}

/-! ## What it means for an implementation to be correct

Meyer: "a program may be viewed as the implementation of a certain function
(`sol`) which must ensure that a certain relation (`goal`) is satisfied between
its argument and its result; in mathematical terms, the function is included in
(is a subset of) the relation."

He allows `sol` to be partial -- "there may be some inputs for which there is no
acceptable solution (those not in the domain of `goal`), so `sol` may be a
partial function" -- which is why the implementation is modelled here as
`Text → Option Text` rather than `Text → Text`. -/

/-- Meyer's correctness conditions, `dom (goal) ⊆ dom (sol)` and `sol ⊆ goal`.

Nothing below uses this.  It is part of the transcription rather than of any
proof: it records what Meyer demands of an implementation, and this development
supplies no implementation to demand it of. -/
def IsCorrect (sol : Text → Option Text) : Prop :=
  (∀ i ∈ DomGoal MAXPOS, (sol i).isSome) ∧
  (∀ i o, sol i = some o → Goal MAXPOS i o)

/-! ## The domain of the specification

Meyer's stated theorem, and the one thing the formal specification tells us that
no natural-language version of the problem does: the problem is solvable exactly
when the input contains no word longer than `MAXPOS`.  He derives it from the
definitions of `TRIMMED` and `max_line_length`. -/

/-- The right-hand side of Meyer's theorem: "the domain of relation `goal`
consists of sequences such that, if a character `c` is followed by `MAXPOS` other
characters, at least one character among `c` and the other characters must be a
break." -/
def NoOversizeWord : Set Text :=
  {s | ∀ t : Text, t.IsInfix s → t.length = MAXPOS + 1 → ∃ c ∈ t, IsBreak c}

/-!
Meyer's two claims about this specification -- that its domain is exactly
`NoOversizeWord`, and that it is genuinely nondeterministic -- are stated and
proved in `Meyer.Facts`.  This module is definitions only.
-/

end Meyer
