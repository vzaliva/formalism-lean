import Meyer.Paper.Facts
import Meyer.Book.Facts

/-!
# The two specifications compared

Meyer's 1985 paper and his 2022 book chapter specify the same problem, in his
words "probably similar in spirit".  They are similar in spirit; they are not the
same relation.

Both build the output in four stages -- compact the runs of separators, exchange
separators for one another, bound the line length, minimise the number of lines --
and both derive the same solvability condition.  They part company over the
separators at the two ends of the text.

* The paper compacts by taking a *longest* subsequence of the input with no two
  adjacent break characters.  A leading break contributes one character to that
  subsequence, so it survives: `COMPACTED (" AB") = {" AB"}`.
* The book compacts by taking a *shortest* recast, and `[L]` and `[T]` delete
  leading and trailing breaks outright.  Meyer notices the consequence and states
  it as `T6`: "Can the output text start or end with a break?  ... the answer is
  no in this version."

The difference is visible, and not only cosmetically.  Take the input `␣AB` with
a line limit of two characters.  The paper's specification cannot leave the
leading blank where it is -- the line `␣AB` is three characters long -- so it must
turn it into a new line, and the unique output has an **empty first line**.  The
book's specification deletes it.

That example needs letters and is worked out at `Char` in
`Meyer.Comparison.Examples`.  What is proved here, for every alphabet, is the
same divergence on the smallest possible input: `specifications_differ` shows
that for the one-character text `[space]` at line limit one each specification's
output is rejected by the other -- the paper keeps the space, the book deletes it
(`T7`) -- and `paper_ne_book` states it as an inequality of relations.  Three
natural strengthenings are *not* proved, and are recorded as remarks:

* that each specification's output for that input is unique;
* that the disagreement is confined to the separators at the two ends, so that
  the two relations coincide on inputs with neither;
* that the disagreement extends to an input of separators only: the book
  yields the empty text, `Meyer.Book.solutions_of_forall_isSeparator`, while the
  1985 specification yields a single space, because its `COMPACTED` again keeps
  one break character.  At `MAXPOS = 0` a space is a line one character long and
  is excluded, and the paper's output for `[space]` is `[new_line]` instead.

The third is what `specifications_differ` proves, for `MAXPOS = 1`.  It settles
against the 1985 specification a question Meyer raises as `T7` and leaves open
for the natural-language originals: "the original specification could be
construed, although not conclusively, to yield a one-space output".
-/

namespace Meyer.Comparison

/-! ## On every alphabet: a lone space

The witness is the one-character text `[space]`, a text of every alphabet.  The
paper compacts it to itself and, at a line limit of one, keeps it; the book
deletes it. -/

section Generic

variable {α : Type*} [DecidableEq α] [Alphabet α]

/-- The 1985 specification keeps a lone space.  Everything reachable from
`[space]` is `[space]` or `[new_line]`, and neither has fewer new lines. -/
private lemma paper_goal_blank : Paper.Goal 1 [(blank : α)] [blank] := by
  have hnd : Paper.NoDoubleBreak [(blank : α)] := List.isChain_singleton _
  refine ⟨⟨[blank], Paper.mem_compacted_self hnd, List.forall₂_same.2 fun _ _ => Or.inl rfl,
    maxRun_le fun t ht _ => by simpa using ht.length_le⟩, fun y hy => ?_⟩
  obtain ⟨b, hb, hy, -⟩ := hy
  obtain rfl : b = [blank] := by
    have hlen := Paper.length_eq_of_mem_compacted hnd hb
    rcases List.sublist_singleton.1 hb.1.1 with rfl | rfl
    · simp at hlen
    · rfl
  rcases y with _ | ⟨c, y⟩
  · exact absurd (List.forall₂_nil_left_iff.1 hy) (List.cons_ne_nil _ _)
  · obtain ⟨hc, hy'⟩ := List.forall₂_cons.1 hy
    obtain rfl : y = [] := List.forall₂_nil_right_iff.1 hy'
    rcases hc with rfl | ⟨hc, -⟩
    · exact le_rfl
    · rcases hc with rfl | rfl
      · exact le_rfl
      · exact (List.count_le_length (a := newline) (l := [blank])).trans
          (by simp [Paper.numberOfNewLines])

/-- The 2022 specification deletes it: `T7`. -/
private lemma not_book_goal_blank : ¬ Book.Goal 1 [(blank : α)] [blank] := by
  intro h
  have h7 := Book.solutions_of_forall_isSeparator (M := 1) (i := [(blank : α)])
    fun c hc => by rw [List.mem_singleton] at hc; exact hc ▸ Or.inl rfl
  rw [Book.Goal, h7, Set.mem_singleton_iff] at h
  exact List.cons_ne_nil _ _ h

/-- The 2022 specification's output for a lone space is the empty text: `T7`. -/
private lemma book_goal_blank_nil : Book.Goal 1 [(blank : α)] [] := by
  have h7 := Book.solutions_of_forall_isSeparator (M := 1) (i := [(blank : α)])
    fun c hc => by rw [List.mem_singleton] at hc; exact hc ▸ Or.inl rfl
  rw [Book.Goal, h7]
  exact Set.mem_singleton _

/-- The 1985 specification rejects the empty text: everything reachable from
`[space]` has one character. -/
private lemma not_paper_goal_blank_nil : ¬ Paper.Goal 1 [(blank : α)] [] := by
  rintro ⟨⟨b, hb, hy, -⟩, -⟩
  have h1 := Paper.length_eq_of_mem_equivalent hy
  have h2 := Paper.length_eq_of_mem_compacted (List.isChain_singleton _) hb
  simp only [List.length_nil, List.length_singleton] at h1 h2
  omega

/-- **The two specifications are not the same relation**, on every alphabet.

For the input `[space]` with a line limit of one, each of Meyer's two
specifications produces an output that the other rejects: the 1985 one keeps
the space, the 2022 one deletes it.

One separating example is enough to show the relations differ, which is all this
states.  Where they differ, and whether they agree elsewhere, is discussed in the
module header and is not proved. -/
theorem specifications_differ :
    ∃ (M : ℕ) (i o₁ o₂ : Text α),
      Paper.Goal M i o₁ ∧ ¬ Book.Goal M i o₁ ∧
      Book.Goal M i o₂ ∧ ¬ Paper.Goal M i o₂ :=
  ⟨1, [blank], [blank], [], paper_goal_blank, not_book_goal_blank, book_goal_blank_nil,
    not_paper_goal_blank_nil⟩

/-- The same, as an inequality of relations: the two are different elements of
`Spec α`. -/
theorem paper_ne_book : ∃ M : ℕ, (Paper.Goal M : Spec α) ≠ Book.Goal M :=
  ⟨1, fun h => not_book_goal_blank (h ▸ paper_goal_blank)⟩

end Generic

end Meyer.Comparison
