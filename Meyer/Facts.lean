import Meyer.Retention

/-!
# Meyer's two claims about his specification

`Meyer.Spec` transcribes the specification; this module proves the two things
Meyer asserts about it.  Both hold.

* `goal_not_functional` -- the specification is genuinely nondeterministic.
* `domGoal_eq_noOversizeWord` -- the problem is solvable exactly for texts with
  no word longer than `MAXPOS`.

The second follows Meyer's own derivation sentence by sentence, with
`Meyer.Retention.mem_noOversizeWord_compacted_iff` supplying the one step he
takes silently.
-/

namespace Meyer

/-! ## The specification is nondeterministic

Meyer: "there may be more than one correct output for a given input; in other
words, a truly general specification of the problem should be nondeterministic."

The witness is his own, from his analysis of the ambiguity in Goodenough and
Gerhart's prose: with `MAXPOS = 10` and the input `WHO WHAT WHEN` "there are two
equally correct two-line solutions (`WHAT` may be on either the first or second
line)".  Their specification, he suspects, was nondeterministic by accident;
his is so by design, and the formal `goal` does relate the input to both. -/

section Nondeterminism

/-- Meyer's input, `WHO WHAT WHEN`. -/
private def wIn : Text := "WHO WHAT WHEN".toList

/-- One acceptable output: `WHAT` on the first line. -/
private def wOut₁ : Text := "WHO WHAT\nWHEN".toList

/-- The other: `WHAT` on the second line. -/
private def wOut₂ : Text := "WHO\nWHAT WHEN".toList

private lemma wIn_noDoubleBreak : NoDoubleBreak wIn := by decide

private lemma wIn_mem_compacted : wIn ∈ Compacted wIn :=
  mem_compacted_self wIn_noDoubleBreak

/-- Anything reachable from the input has its length: `COMPACTED` preserves it
because the input already has single breaks, and `EQUIVALENT` preserves it by
definition. -/
private lemma length_of_mem_transf {y : Text} (hy : y ∈ Transf 10 wIn) :
    y.length = 13 := by
  obtain ⟨b, hb, hEquiv, -⟩ := hy
  rw [length_eq_of_mem_equivalent hEquiv, length_eq_of_mem_compacted wIn_noDoubleBreak hb]
  decide

/-- Every acceptable output has at least one newline: without one it would be a
single line of thirteen characters, and `MAXPOS` is ten. -/
private lemma one_le_newlines {y : Text} (hy : y ∈ Transf 10 wIn) :
    1 ≤ numberOfNewLines y := by
  by_contra hcon
  have hzero : numberOfNewLines y = 0 := by omega
  have hnot : newline ∉ y := List.count_eq_zero.1 hzero
  have hlen : y.length = 13 := length_of_mem_transf hy
  have hbound : maxLineLength y ≤ 10 := hy.choose_spec.2.2
  have := length_le_maxLineLength_of_no_newline hnot
  omega

/-- A text equivalent to the input that fits within `MAXPOS` and has exactly one
newline is an acceptable output, since nothing acceptable has fewer. -/
private lemma goal_of_one_newline {o : Text} (ho : o ∈ Equivalent wIn)
    (hmax : maxLineLength o ≤ 10) (h1 : numberOfNewLines o = 1) : Goal 10 wIn o :=
  ⟨⟨wIn, wIn_mem_compacted, ho, hmax⟩, fun y hy => by rw [h1]; exact one_le_newlines hy⟩

private lemma goal_wOut₁ : Goal 10 wIn wOut₁ :=
  goal_of_one_newline (by decide) (maxLineLength_le_of_tails (by decide)) (by decide)

private lemma goal_wOut₂ : Goal 10 wIn wOut₂ :=
  goal_of_one_newline (by decide) (maxLineLength_le_of_tails (by decide)) (by decide)

/-- **Meyer's nondeterminism claim.**  "There may be more than one correct output
for a given input; in other words, a truly general specification of the problem
should be nondeterministic." -/
theorem goal_not_functional :
    ∃ (n : ℕ) (i o₁ o₂ : Text), Goal n i o₁ ∧ Goal n i o₂ ∧ o₁ ≠ o₂ :=
  ⟨10, wIn, wOut₁, wOut₂, goal_wOut₁, goal_wOut₂, by decide⟩

end Nondeterminism

/-! ## The domain of the specification

Meyer's other claim:

> `dom (goal) = {s | ∀i ∈ 1..length (s) − MAXPOS, ∃j ∈ i..i + MAXPOS, s (j) ∈ BREAK_CHAR}`

His derivation is a paragraph of three sentences, and the proof below follows
them in order.

1. "It is trivial to prove that, given a sequence of characters `a`, there is
   always at least one sequence `b` such that relation `short_breaks (a, b)`
   holds."  That is `compacted_nonempty`.

2. "Given `b`, however, the necessary and sufficient condition for the existence
   of at least one sequence `c` such that `limited_length (b, c)` holds is that
   `b` contains no word (i.e., contiguous subsequence of non-break characters)
   of length greater than `MAXPOS`."  That is `trimmed_nonempty_iff`.  Neither
   direction needs a wrapping algorithm: for sufficiency, put every word on a
   line of its own.

3. "Thus, the domain of definition of the relation `tr`, which is also the
   domain of the function `TRANSF` and thus of the relation `goal`, is the set
   of input texts containing no word longer than `MAXPOS`."  Sentence 2 is about
   the *compacted* text `b`; sentence 3 is about the *input*.  Passing from one
   to the other needs to know that compaction leaves the words alone, which
   Meyer asserted a page earlier in a parenthetical remark and did not prove; it
   is `Meyer.Retention`.  That `FEWEST_LINES` does not empty a nonempty set is
   `mem_domGoal_iff`.

Neither step is a defect in the paper, unlike the subsequence definition handled
in `Meyer.Bug`. -/

variable (MAXPOS : ℕ)

/-- **Meyer's condition for `limited_length` to be satisfiable.**  "The necessary
and sufficient condition for the existence of at least one sequence `c` such that
`limited_length (b, c)` holds is that `b` contains no word ... of length greater
than `MAXPOS`." -/
theorem trimmed_nonempty_iff (b : Text) :
    (Trimmed MAXPOS b).Nonempty ↔ b ∈ NoOversizeWord MAXPOS :=
  ⟨fun ⟨_, hc⟩ => mem_noOversizeWord_of_mem_trimmed hc, trimmed_nonempty⟩

/-- **Meyer's theorem on the domain of `goal`.** -/
theorem domGoal_eq_noOversizeWord : DomGoal MAXPOS = NoOversizeWord MAXPOS := by
  ext i
  rw [mem_domGoal_iff]
  constructor
  · rintro ⟨c, b, hb, hc⟩
    exact (mem_noOversizeWord_compacted_iff MAXPOS hb).1
      ((trimmed_nonempty_iff MAXPOS b).1 ⟨c, hc⟩)
  · intro hi
    obtain ⟨b, hb⟩ := compacted_nonempty i
    obtain ⟨c, hc⟩ :=
      (trimmed_nonempty_iff MAXPOS b).2 ((mem_noOversizeWord_compacted_iff MAXPOS hb).2 hi)
    exact ⟨c, b, hb, hc⟩

end Meyer
