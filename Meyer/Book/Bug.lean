import Meyer.Book.Facts
import Mathlib.Data.Set.Card

/-!
# `M3` read literally

`Meyer/Book/Spec.lean` transcribes `new_lines` as Meyer's prose describes it,
"the number of `new_line` characters in `out`".  This module formalises what his
formula actually says and shows that the difference matters.

## The defect

`M3` is

> `new_lines (out) ≜ |{x: range out | x = new_line}|`

where `|A|` is the cardinal of `A`.  Meyer writes it with a bar over `A`, and gives
`|A|` as the alternative notation (p. 162); the bar does not survive into plain
text, so `|A|` is used throughout this development.  `range` is defined in 9.2.6,
where Meyer is explicit that it collapses repetitions:

> While a set is only characterized by which elements belong to it, sequences
> imply an additional notion of order: `[0, 1, 2]` and `[2, 0, 1]` have the same
> range, `{0, 1, 2}`, but are different sequences.  Also, an element may appear
> twice, a concept that would be meaningless for sets: `[1, 2, 2]` and `[1, 2]`
> have the same range, `{1, 2}`, but are different sequences.

So `{x: range out | x = new_line}` is a subset of the one-element set
`{new_line}`, and `new_lines (out)` is `0` or `1` -- never the number of new
lines (`newLines_le_one`).  What Meyer wanted was an index set: `{i: domain out |
out (i) = new_line}`, which is what he wrote in 1985 (`card {i ∈ 1..length (s) |
s (i) = new_line}`).  The other uses of `range` in the chapter, in `M4` and `M5`,
are memberships rather than counts and are correct.

## What goes wrong

`S1` minimises `new_lines (out)` last.  Read literally, that measure only
distinguishes "has a new line" from "has none", so the minimisation is decided
only when some candidate fits on a single line; whenever the text actually has to
be wrapped, every candidate scores `1` and the requirement is vacuous.

**The specification stops asking that lines be filled.**  On Meyer's own example
(p. 176) -- the input `␣␣ABC␣␣D␣␣EFG` at `M = 5`, for which he displays the two
solutions `ABC␣D / EFG` and `ABC / D␣EFG` -- the literal reading admits a third,
`ABC / D / EFG`, on three lines where two suffice.  That is
`goal_unfilled` below.

## Why it survived

No theorem in the chapter can see it.  `T8`, the one substantial result, asks
only whether the set of solutions is non-empty, and minimising a different
measure over the same non-empty set still leaves it non-empty.  All eight of the
chapter's properties stay true under the reading formalised below, so proving
them, by hand or by machine, would not have found it.

The 1985 defect is the opposite case.  It makes Meyer's own domain theorem false,
so mechanising the paper catches it at once
(`Meyer.Paper.Bug.domGoal_subset_breaksOnly`); it survived only because the
derivation was three sentences of prose that silently used the intended meaning
of "subsequence".  The two are the two ways a formal specification goes wrong:
one is caught by checking the argument, the other only by reading each definition
against the problem it is meant to describe.

## What is and is not claimed

The literal reading is the more permissive of the two, exactly as in the paper:
it accepts every output the intended reading accepts and more
(`solutions_subset`).  Nothing Meyer proves becomes false; what fails is the
specification's agreement with the problem it is specifying.  In particular this
is a weaker failure than the paper's, where `COMPACTED` came out empty and the
relation `goal` related nothing to anything.
-/

namespace Meyer.Book.Bug

section Literal

variable {α : Type*} [DecidableEq α] [Alphabet α]

open Meyer.Book

/-! ## The literal definition -/

/-- `range s`: "the set of its values", 9.2.6. -/
def range (s : Text α) : Set α :=
  {c | c ∈ s}

/-- **`M3` taken literally**: `|{x: range out | x = new_line}|`. -/
noncomputable def newLines (s : Text α) : ℕ :=
  Set.ncard {c ∈ range s | c = newline}

/-- The whole of the defect: the measure is a membership test. -/
lemma newLines_eq (s : Text α) : newLines s = if newline ∈ s then 1 else 0 := by
  by_cases h : newline ∈ s
  · rw [if_pos h, newLines, show {c ∈ range s | c = newline} = {newline} by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, range]
      exact ⟨fun hc => hc.2, fun hc => ⟨hc ▸ h, hc⟩⟩]
    exact Set.ncard_singleton _
  · rw [if_neg h, newLines, show {c ∈ range s | c = newline} = ∅ by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, range]
      rintro ⟨hc, rfl⟩; exact h hc]
    exact Set.ncard_empty _

/-- However many lines a text has, the literal `M3` never exceeds one. -/
theorem newLines_le_one (s : Text α) : newLines s ≤ 1 := by
  rw [newLines_eq]; split <;> omega

/-! ## The specification under the literal reading

`S1` again, with `Meyer.Book.newLines` replaced by the literal `newLines`.  The
names shadow those of `Meyer.Book` on purpose. -/

/-- `S1` with `M3` read literally. -/
noncomputable def Solutions (M : ℕ) (i : Text α) : Set (Text α) :=
  Mu (MinRecasts i) (fun o => maxLine o ≤ M) newLines

/-- The relation it defines. -/
def Goal (M : ℕ) (i o : Text α) : Prop :=
  o ∈ Solutions M i

/-- **The defect adds outputs and removes none.**  Every output the intended
reading accepts, the literal one accepts too. -/
theorem solutions_subset (M : ℕ) (i : Text α) :
    Meyer.Book.Solutions M i ⊆ Solutions M i := by
  rintro o ⟨ho, hmin⟩
  refine ⟨ho, fun y hy => ?_⟩
  rw [newLines_eq, newLines_eq]
  split
  · rename_i hno
    rw [if_pos]
    exact List.count_pos_iff.1 (Nat.lt_of_lt_of_le (List.count_pos_iff.2 hno) (hmin y hy))
  · exact Nat.zero_le _

end Literal

/-! ## The witness

`T5`'s input, `c cc c` at `M = 4`, with a third output. -/

section Witness

variable {α : Type*} [Lettered α]

/-- `c / cc / c`: three lines where two are enough. -/
private def tOut₃ (c : α) : Text α := [c, newline, c, c, newline, c]

private lemma recast_tOut₃ (c : α) : Recast (tIn c) (tOut₃ c) :=
  recast_trans (recast_tOut₁ c) (recast_of_recast1 (by
    simpa [tOut₁, tOut₃] using recast1_replace (b := [blank]) (x := [c])
      (y := [c, c, newline, c]) (singleton_mem_break (Or.inl rfl)) (s := newline) (Or.inr rfl)))

/-- Under the literal `M3`, a three-line output is as good as a two-line one. -/
private lemma goal_tOut₃ [DecidableEq α] {c : α} (hc : ¬ IsBreak c) :
    Goal 4 (tIn c) (tOut₃ c) := by
  refine ⟨⟨mem_minRecasts_of_length_six hc (recast_tOut₃ c) rfl,
    maxLine_le_four (x := [c]) (y := [c, c, newline, c]) (by simp) (by simp)⟩, fun y hy => ?_⟩
  rw [newLines_eq, newLines_eq, if_pos (by simp [tOut₃] : newline ∈ tOut₃ c),
    if_pos (List.count_pos_iff.1 (one_le_newLines_tIn hc hy.1 hy.2))]

/-- It is not a solution of the specification Meyer describes: it has two new
lines where `c cc / c` has one. -/
private lemma not_goal_tOut₃ [DecidableEq α] {c : α} (hc : ¬ IsBreak c)
    (h : (blank : α) ≠ newline) :
    ¬ Meyer.Book.Goal 4 (tIn c) (tOut₃ c) := by
  intro hg
  have hcn : c ≠ newline := fun e => hc (Or.inr e)
  obtain ⟨-, hmin⟩ := mem_solutions_iff.1 hg
  obtain ⟨⟨h₁, h₂⟩, -⟩ := mem_solutions_iff.1 (goal_tOut₁ hc h)
  have := hmin (tOut₁ c) h₁ h₂
  rw [show Meyer.Book.newLines (tOut₃ c) = 2 from by simp [Meyer.Book.newLines, tOut₃, hcn],
    show Meyer.Book.newLines (tOut₁ c) = 1 from by simp [Meyer.Book.newLines, tOut₁, hcn, h]]
    at this
  omega

/-- **The defect.**  On any alphabet with a letter and two distinct separators,
the specification as written accepts an output that puts each word on its own
line; the specification as described does not.  Meyer's own example,
`␣␣ABC␣␣D␣␣EFG` at `M = 5` with the third output `ABC / D / EFG`, is in
`Meyer.Book.Examples`.

Meyer displays two solutions for his input and asks the reader to notice that
there is more than one.  There are more than he thinks: the requirement that
lines be filled has gone. -/
theorem goal_unfilled [DecidableEq α] (h : (blank : α) ≠ newline) :
    ∃ (M : ℕ) (i o : Text α), Goal M i o ∧ ¬ Meyer.Book.Goal M i o := by
  obtain ⟨c, hc⟩ := Lettered.exists_letter (α := α)
  exact ⟨4, tIn c, tOut₃ c, goal_tOut₃ hc, not_goal_tOut₃ hc h⟩

end Witness

end Meyer.Book.Bug
