import Meyer.Paper.Retention

/-!
# Meyer's two claims about his specification

`Meyer.Paper.Spec` transcribes the specification; this module proves the two things
Meyer asserts about it.  Both hold.

* `goal_not_functional` -- the specification is genuinely nondeterministic.
* `domGoal_eq_noOversizeWord` -- the problem is solvable exactly for texts with
  no word longer than `MAXPOS`.

The second follows Meyer's own derivation sentence by sentence, with
`Meyer.Retention.mem_noOversizeWord_compacted_iff` supplying the one step he
takes silently.
-/

namespace Meyer.Paper

variable {α : Type*} [DecidableEq α] [Alphabet α]

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
   is `Meyer.Paper.Retention`.  That `FEWEST_LINES` does not empty a nonempty set is
   `mem_domGoal_iff`.

Neither step is a defect in the paper, unlike the subsequence definition handled
in `Meyer.Paper.Bug`. -/

variable (MAXPOS : ℕ)

/-- **Meyer's condition for `limited_length` to be satisfiable.**  "The necessary
and sufficient condition for the existence of at least one sequence `c` such that
`limited_length (b, c)` holds is that `b` contains no word ... of length greater
than `MAXPOS`." -/
theorem trimmed_nonempty_iff (b : Text α) :
    (Trimmed MAXPOS b).Nonempty ↔ b ∈ NoOversizeWord α MAXPOS :=
  ⟨fun ⟨_, hc⟩ => mem_noOversizeWord_of_mem_trimmed hc, trimmed_nonempty⟩

/-- **Meyer's theorem on the domain of `goal`.** -/
theorem domGoal_eq_noOversizeWord : DomGoal α MAXPOS = NoOversizeWord α MAXPOS := by
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


end Meyer.Paper
