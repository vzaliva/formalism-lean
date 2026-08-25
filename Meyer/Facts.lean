/-
Copyright (c) 2026 Vadim Zaliva. All rights reserved.
-/
import Meyer.Retention

/-!
# Meyer's two claims about his specification

`Meyer.Spec` transcribes the specification; this module proves the two things
Meyer asserts about it.  Both hold.

* `goal_not_functional` — the specification is genuinely nondeterministic.
* `domGoal_eq_noOversizeWord` — the problem is solvable exactly for texts with no
  word longer than `MAXPOS`.

The second is proved first for texts whose breaks are already single, which is
the case Meyer's own phrasing addresses, and then in general using
`Meyer.Retention.mem_noOversizeWord_compacted_iff` — the step he asserts in a
parenthesis and does not prove.
-/

namespace Meyer

/-! ## The specification is nondeterministic

Meyer's own witness is `MAXPOS = 10` with input `WHO WHAT WHEN`, where `WHAT`
may go on either line and both two-line outputs are acceptable.  The proof below
uses a minimal instance of the same tie — `MAXPOS = 3` and `a b c`, five
characters instead of thirteen — which keeps the decision procedures small.  The
phenomenon is identical: the text does not fit on one line, exactly one break
must become a newline, and either of the two breaks will do. -/

section Nondeterminism

/-- The input of the witness: `a b c`. -/
private def wIn : Text := ['a', ' ', 'b', ' ', 'c']

/-- One acceptable output: break at the first blank. -/
private def wOut₁ : Text := ['a', '\n', 'b', ' ', 'c']

/-- The other: break at the second blank. -/
private def wOut₂ : Text := ['a', ' ', 'b', '\n', 'c']

private theorem wIn_noDoubleBreak : NoDoubleBreak wIn := by decide

private theorem wIn_mem_compacted : wIn ∈ Compacted wIn :=
  mem_compacted_self wIn_noDoubleBreak

/-- Anything reachable from `a b c` has its length: `COMPACTED` preserves it
because `a b c` already has single breaks, and `EQUIVALENT` preserves it by
definition. -/
private theorem length_of_mem_transf {y : Text} (hy : y ∈ Transf 3 wIn) :
    y.length = 5 := by
  obtain ⟨b, hb, hEquiv, -⟩ := hy
  have hb5 : b.length = 5 := length_eq_of_mem_compacted wIn_noDoubleBreak hb
  rw [length_eq_of_mem_equivalent hEquiv, hb5]

/-- Every acceptable output has at least one newline: without one it would be a
single line of five characters, and `MAXPOS` is three. -/
private theorem one_le_newlines {y : Text} (hy : y ∈ Transf 3 wIn) :
    1 ≤ numberOfNewLines y := by
  by_contra hcon
  have hzero : numberOfNewLines y = 0 := by omega
  have hnot : newline ∉ y := List.count_eq_zero.1 hzero
  have hlen : y.length = 5 := length_of_mem_transf hy
  have hbound : maxLineLength y ≤ 3 := hy.choose_spec.2.2
  have := length_le_maxLineLength_of_no_newline hnot
  omega

private theorem goal_wOut₁ : Goal 3 wIn wOut₁ := by
  refine ⟨⟨wIn, wIn_mem_compacted, by decide, maxLineLength_le_of_tails (by decide)⟩, ?_⟩
  intro y hy
  have : numberOfNewLines wOut₁ = 1 := by decide
  rw [this]
  exact one_le_newlines hy

private theorem goal_wOut₂ : Goal 3 wIn wOut₂ := by
  refine ⟨⟨wIn, wIn_mem_compacted, by decide, maxLineLength_le_of_tails (by decide)⟩, ?_⟩
  intro y hy
  have : numberOfNewLines wOut₂ = 1 := by decide
  rw [this]
  exact one_le_newlines hy

/-- **Meyer's nondeterminism claim.**  "There may be more than one correct output
for a given input; in other words, a truly general specification of the problem
should be nondeterministic." -/
theorem goal_not_functional :
    ∃ (n : ℕ) (i o₁ o₂ : Text), Goal n i o₁ ∧ Goal n i o₂ ∧ o₁ ≠ o₂ :=
  ⟨3, wIn, wOut₁, wOut₂, goal_wOut₁, goal_wOut₂, by decide⟩

end Nondeterminism

/-! ## The domain of the specification

Meyer's other claim:

> `dom (goal) = {s | ∀i ∈ 1..length (s) − MAXPOS, ∃j ∈ i..i + MAXPOS, s (j) ∈ BREAK_CHAR}`

He derives it in a paragraph, and the derivation is correct.  Both inclusions
turn on a single step he takes silently.  His own words are that the condition
for a solution to exist is that **`b`** — the *compacted* text — has no word
longer than `MAXPOS`; the theorem is then stated about the *input*.  Passing
between the two needs retention, which he asserts one page earlier in a
parenthesis and does not prove; it is `Meyer.Retention`.

The rest is short:

* `⊆` is `domGoal_subset_noOversizeWord_of_noDoubleBreak` below with `b` in place
  of `i` — the remainder is `infix_of_mem_equivalent` and `le_maxLineLength`.
* `⊇` needs no wrapping algorithm.  Replace *every* break of `b` with a newline:
  each line is then a single word of `b`, hence of `a`, hence at most `MAXPOS`
  long, so `TRIMMED (b)` is nonempty.  `FEWEST_LINES` only has to be nonempty,
  which follows from the well-ordering of `ℕ`; it does not have to be computed.

Neither step is a defect in the paper, unlike the subsequence definition handled
in `Meyer.Literal`.  Both of Meyer's claims here are true, and both are now
proved. -/

variable (MAXPOS : ℕ)

/-- **The `⊆` direction, for inputs whose breaks are already single.**  Here
`COMPACTED (i)` is just `{i}`, so the argument runs without the retention lemma:
a break-free stretch of `i` survives into any equivalent text, and a stretch of
`MAXPOS + 1` characters would then be a line longer than `MAXPOS`. -/
theorem domGoal_subset_noOversizeWord_of_noDoubleBreak {i : Text} (h : NoDoubleBreak i)
    (hi : i ∈ DomGoal MAXPOS) : i ∈ NoOversizeWord MAXPOS := by
  obtain ⟨o, ⟨b, hb, hEquiv, hMax⟩, -⟩ := hi
  rw [eq_of_mem_compacted h hb] at hEquiv
  intro t ht hlen
  by_contra hcon
  push Not at hcon
  have hnl : newline ∉ t := fun hmem => hcon newline hmem (Or.inr rfl)
  have := le_maxLineLength (infix_of_mem_equivalent hEquiv ht hcon) hnl
  omega

/-- **The `⊇` direction, for inputs whose breaks are already single.**  Put every
word on a line of its own.  That is acceptable precisely because no word is
longer than `MAXPOS`, and `FEWEST_LINES` only has to be nonempty. -/
theorem noOversizeWord_subset_domGoal_of_noDoubleBreak {i : Text} (h : NoDoubleBreak i)
    (hi : i ∈ NoOversizeWord MAXPOS) : i ∈ DomGoal MAXPOS := by
  rw [mem_domGoal_iff]
  obtain ⟨c, hc⟩ := trimmed_nonempty hi
  exact ⟨c, i, mem_compacted_self h, hc⟩

/-- **Meyer's domain theorem for texts whose breaks are already single.**  This
is the case his own sentence is about: he states the solvability condition in
terms of the compacted text, and only afterwards transfers it to the input. -/
theorem mem_domGoal_iff_of_noDoubleBreak {i : Text} (h : NoDoubleBreak i) :
    i ∈ DomGoal MAXPOS ↔ i ∈ NoOversizeWord MAXPOS :=
  ⟨domGoal_subset_noOversizeWord_of_noDoubleBreak MAXPOS h,
    noOversizeWord_subset_domGoal_of_noDoubleBreak MAXPOS h⟩

/-- **Meyer's theorem on the domain of `goal`.** -/
theorem domGoal_eq_noOversizeWord : DomGoal MAXPOS = NoOversizeWord MAXPOS := by
  ext i
  obtain ⟨b, hb⟩ := compacted_nonempty i
  rw [mem_domGoal_iff]
  constructor
  · rintro ⟨c, b', hb', hc⟩
    have hb'nd : NoDoubleBreak b' := hb'.1.2
    have hb'dom : b' ∈ DomGoal MAXPOS :=
      (mem_domGoal_iff MAXPOS b').2 ⟨c, b', mem_compacted_self hb'nd, hc⟩
    exact (mem_noOversizeWord_compacted_iff MAXPOS hb').1
      ((mem_domGoal_iff_of_noDoubleBreak MAXPOS hb'nd).1 hb'dom)
  · intro hi
    obtain ⟨c, hc⟩ := trimmed_nonempty ((mem_noOversizeWord_compacted_iff MAXPOS hb).2 hi)
    exact ⟨c, b, hb, hc⟩

end Meyer
