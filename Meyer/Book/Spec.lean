import Meyer.Common
import Mathlib.Logic.Relation

/-!
# Meyer's second specification of the text-formatting problem

A transcription into Lean of section 9.5, "An example: text formatting,
revisited", of

> Bertrand Meyer, *Handbook of Requirements and Business Analysis*, Springer,
> 2022.  Chapter 9, "Benefiting from formal methods", pp. 171-185.

Meyer returns there to the problem of `Meyer.Paper` -- Naur's, by way of
Goodenough and Gerhart -- and specifies it again, having, by his own account,
"hardly looked at" the 1985 solution and restarted from scratch.  The result is
the same four-stage pipeline in quite different machinery.

## The two specifications side by side

| stage | 1985 paper | 2022 book |
|---|---|---|
| compaction | `MAX_SET (SINGLE_BREAKS (a), length)` | minimise `out.count` over `recast ({in})` |
| separator exchange | `EQUIVALENT (b)` | folded into `recast1`, case `[R]` |
| line limit | `TRIMMED`: `max_line_length ≤ MAXPOS` | condition `maxline (out) ≤ M` |
| fewest lines | `MIN_SET (-, number_of_new_lines)` | minimise `new_lines (out)` |

The paper reaches the compacted text by taking a longest subsequence with no two
adjacent break characters; the book reaches it by taking a shortest element of
the reflexive transitive closure of a local rewriting relation.  The book's
route is the more tractable of the two: a closure comes with an induction
principle, which is exactly what `Meyer.Paper.Retention` had to do without.

The two are **not** the same relation.  The paper's compaction retains one break
character at the beginning and end of the text; the book's `[L]` and `[T]` delete
them (his `T6`).  On the input `␣AB` with a line limit of two characters the
paper's specification produces an output with an empty first line and the book's
produces one with the blank removed, and each rejects the other's:
`Meyer.Comparison.specifications_differ`.

## This module

Definitions only, following the repository's convention.  Meyer's names are kept,
with `CamelCase` for `Set`- and `Prop`-valued definitions; his labels (`M1`,
`S1`, `[L]`, `[R]`, `[T]`) are quoted in the docstrings.  The theorems `T1` to
`T8` are in `Meyer.Book.Facts`, and the exercise-9-E.6 material about words and
breaks in `Meyer.Book.Words`.

## Deviations from the book

* `LETTER` is kept abstract in the book, subject to `CHARACTER ≜ LETTER ∪
  SEPARATOR`, `LETTER ≠ ∅` and `LETTER ∩ SEPARATOR = ∅` (p. 172).  Identifying
  `CHARACTER` with Lean's `Char` leaves exactly one reading of `LETTER` that
  satisfies all three, the complement of `SEPARATOR`, and that is what is used
  here.  The union equation is what makes M5 and M6 define the same function, so
  it is realised rather than assumed.

* `S1` binds `u` but states its conditions and measures in terms of `out`.  We
  read the bound variable as `out`, which is what the surrounding text (9.5.4,
  the four bullets on p. 175) describes.

* `BREAK ≜ SEPARATOR⁺` uses a `⁺` on sets of sequences that 9.2 does not define
  (it defines `A*` for sequences, and `r⁺` for relations).  We read it in the
  usual way, as the non-empty sequences of separators.

* `M3` is transcribed as Meyer's prose has it, "the number of `new_line`
  characters in `out`", not as his formula has it.  The two differ, and
  `Meyer.Book.Bug` is about the difference.

* The `mu` operator is rendered with `MinSet`, "no element of the set does
  better", in place of Meyer's finiteness side condition; over `ℕ` a nonempty
  set always has a minimum, so nothing is lost.  See `Meyer.Common.minSet_nonempty`,
  which is his "minimization lemma" (exercise 9-E.5) in the half he uses.
-/

namespace Meyer.Book

/-! ## Characters

`CHARACTER ≜ LETTER ∪ SEPARATOR` with `SEPARATOR ≜ {space, new_line}`.  Note the
book's vocabulary: a *separator* is one character, a *break* is one or more.
The paper used *break character* for the former and had no name for the
latter. -/

/-- `SEPARATOR ≜ {space, new_line}`.  This is the paper's `BREAK_CHAR`. -/
abbrev IsSeparator (c : Char) : Prop := IsBreak c

/-- `LETTER`: everything that is not a separator.  Meyer keeps the set abstract,
subject to `CHARACTER ≜ LETTER ∪ SEPARATOR`, `LETTER ≠ ∅` and
`LETTER ∩ SEPARATOR = ∅`.  Once `CHARACTER` is `Char`, the complement of
`SEPARATOR` is the only set satisfying all three. -/
def IsLetter (c : Char) : Prop := ¬ IsSeparator c

instance : DecidablePred IsLetter :=
  fun c => inferInstanceAs (Decidable (¬ IsBreak c))

/-- `BREAK ≜ SEPARATOR⁺`: a non-empty sequence of separators. -/
def Break : Set Text :=
  {b | b ≠ [] ∧ ∀ c ∈ b, IsSeparator c}

/-! ## Recasting

The relation at the heart of the specification.  Meyer's box, in full:

> **Definition of `recast1` (`in`, `out`: `TEXT`) (a boolean property)**
>
> `∃ b: BREAK |`
> `  in = b + out ∨`                                       -- `[L]` Removal of a leading break
> `  in = out + b ∨`                                       -- `[T]` Removal of a trailing break
> `  ∃ s: SEPARATOR, x, y: TEXT |`
> `    (in = x + b + y ∧ out = x + [s] + y)`   -- `[R]` Replacement of a break
>                                              --     by a single separator

Note the direction: the relation says how `in` may be recovered from `out`, not
how `out` is computed from `in`.  Meyer draws attention to this himself (9.5.2):
"You will probably have noted the unexpected direction in which the
specification works". -/

/-- **`recast1`.**  The three ways in which `out` may differ from `in` by one
step: `[L]`, `[T]`, `[R]`. -/
def Recast1 (i o : Text) : Prop :=
  ∃ b ∈ Break,
    i = b ++ o ∨
    i = o ++ b ∨
    ∃ s, IsSeparator s ∧ ∃ x y : Text, i = x ++ b ++ y ∧ o = x ++ [s] ++ y

/-- `recast ≜ recast1*`, the reflexive transitive closure.  Meyer: "This is where
the power and beauty of reflexive transitive closure strike: `recast` ... gives
us all possible variants of `in`, including those without any useless
separators." -/
def Recast : Text → Text → Prop :=
  Relation.ReflTransGen Recast1

/-- `recast ({in})`, the image of the one-element set `{in}` under `recast`. -/
def RecastImage (i : Text) : Set Text :=
  {o | Recast i o}

/-! ## Measures

`M3` to `M6`.  `maxline` (M5) is character for character the paper's
`max_line_length`; `maxword` (M4) has no counterpart in the paper, which states
the same condition as a bound on stretches of `MAXPOS + 1` characters. -/

/-- `new_lines (out)`: "the number of `new_line` characters in `out`".

This is `M3` as Meyer's prose describes it.  His formula says something else --
it counts the *distinct values* of `out` equal to `new_line`, of which there is
at most one -- and `Meyer.Book.Bug` proves that the difference matters.  Meyer's
parenthetical is a good statement of the intent: "What we really want to
minimize is the number of *lines*, but since it is `new_lines (out) + 1` we can
for simplicity minimize `new_lines` instead." -/
def newLines (s : Text) : ℕ :=
  s.count newline

/-- `maxword (in) ≜ max (s.count | s ∈ SUBSEQ (in) ∧ range s ⊆ LETTER)`: the
length of the longest run of consecutive letters.  A member of `SUBSEQ` is a
contiguous stretch (9.2.6), which is `List.IsInfix`. -/
noncomputable def maxWord (s : Text) : ℕ :=
  maxRun IsLetter s

/-- `maxline (in) ≜ max (s.count | s ∈ SUBSEQ (in) ∧ new_line ∉ range s)`: the
length of the longest run of consecutive characters containing no `new_line`.

This is the paper's `max_line_length` verbatim, `Meyer.Paper.maxLineLength`; the
two modules keep their own copy so that each stands as a transcription of its own
source. -/
noncomputable def maxLine (s : Text) : ℕ :=
  maxRun (fun c => c ≠ newline) s

/-! ## Words and breaks

`WORDS (t)` and `breaks (t)`, "respectively the sequences of words and breaks of
a text `t`", used in `T3` and `T4`.  The book does not define them: exercise
9-E.6 asks the reader to, from the hint that `t` can be written in exactly one
way as `b₀ + Σᵢ (wᵢ + bᵢ)` with the `wᵢ` non-empty words and the `bᵢ` non-empty
breaks except possibly `b₀` or `bₙ`.

We take both to be the *non-empty* maximal runs, so that `b₀` and `bₙ` are listed
only when they are there.  That is the convention `T4` needs: under the other
one, in which an absent `b₀` is still counted, `T3` makes the two break counts
equal and `T4` says nothing.  Meyer's justification of `T4` -- "these
transformations only affect the number of breaks except by possibly removing a
heading break, a trailing break or both" -- is about the convention used here. -/

/-- `WORDS (t)`: the non-empty maximal runs of letters, in order. -/
noncomputable def words (t : Text) : List Text :=
  (t.splitOnP fun c => decide (IsSeparator c)).filter fun w => !w.isEmpty

/-- `breaks (t)`: the non-empty maximal runs of separators, in order. -/
noncomputable def breaks (t : Text) : List Text :=
  (t.splitOnP fun c => decide (IsLetter c)).filter fun b => !b.isEmpty

/-! ## The specification

Meyer's `mu` operator and the one-line specification `S1` built from it. -/

/-- `M1`: `μ a: A | c (a) | m (a)`, "the subset of a set `A` consisting of
elements, if any, that satisfy condition `c` and have minimal value for a
numerical measure `m`". -/
def Mu (A : Set Text) (c : Text → Prop) (m : Text → ℕ) : Set Text :=
  MinSet {a ∈ A | c a} m

/-- The first stage of `S1`: the recasts of `in` of minimum length.

Meyer, in the operational reading of `S1` (p. 175): "From those, we only retain
the ones of minimum length ... Since the transformations involved in `recast1`
only affect breaks, these texts are also the ones with a minimum number of
separators." -/
def MinRecasts (i : Text) : Set Text :=
  Mu (RecastImage i) (fun _ => True) List.length

/-- **`S1`**, the specification.

> `μu: recast ({in}) | True, maxline (out) ≤ M | out.count, new_lines (out)`

By `M2` this is a double application of `M1`: minimise length over the recasts
of `in`, then, among those, impose `maxline ≤ M` and minimise the number of new
lines.  The order matters, and Meyer says so: "the order matters, since
reversing it may yield a different result". -/
noncomputable def Solutions (M : ℕ) (i : Text) : Set Text :=
  Mu (MinRecasts i) (fun o => maxLine o ≤ M) newLines

/-! ### The English restatement of 9.5.7

Meyer follows `S1` with a "formal picnic", a natural-language version meant to
"follow the mathematical definitions faithfully".  Three of its clauses do not.
Clause 4 allows only "replacement of two consecutive separators by a single
separator", which omits `[R]` on a break that is already a single separator, so
the English version can never exchange a space for a new line and cannot produce
most of the outputs `S1` admits.  Clauses 6 and 7 say "largest word length `M`"
and "largest line length `M`" where `S1` requires only that these be at most `M`.

None of this is formalised here: the object of study is `S1`, and the picnic
version is a rendering of it rather than a competing specification. -/

/-- The input/output relation the specification defines, for comparison with the
paper's `goal`. -/
def Goal (M : ℕ) (i o : Text) : Prop :=
  o ∈ Solutions M i

end Meyer.Book
