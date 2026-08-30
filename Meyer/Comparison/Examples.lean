import Meyer.Comparison
import Meyer.Char

/-!
# The separating example, over `Char`

`Meyer.Comparison` separates the two specifications on the one-character text
`[space]`, for every alphabet.  The example the module header tells the story
with, `␣AB` at a line limit of two -- where the 1985 specification must turn the
leading blank into a new line and output an **empty first line**, and the 2022
one deletes the blank -- needs letters, and is worked out here at `Char`, where
`decide` does most of the work.
-/

namespace Meyer.Comparison

/-! ## The witness

A blank, then a two-letter word, with a line limit of two. -/


/-- The input `␣AB`. -/
private def cIn : Text Char := " AB".toList

/-- What the 1985 specification produces: an empty first line. -/
private def cPaper : Text Char := "\nAB".toList

/-- What the 2022 specification produces: the blank is gone. -/
private def cBook : Text Char := "AB".toList

/-! ## The paper's answer -/

private lemma cIn_noDoubleBreak : Paper.NoDoubleBreak cIn := by decide

/-- Everything the paper's specification can reach from `␣AB` has three
characters: compaction cannot shorten a text that already has single breaks, and
break substitution never changes a length. -/
private lemma length_of_mem_transf {y : Text Char} (hy : y ∈ Paper.Transf 2 cIn) :
    y.length = 3 := by
  obtain ⟨b, hb, hEquiv, -⟩ := hy
  rw [Paper.length_eq_of_mem_equivalent hEquiv,
    Paper.length_eq_of_mem_compacted cIn_noDoubleBreak hb]
  decide

/-- So none of them fits on a single line of two characters. -/
private lemma one_le_newlines {y : Text Char} (hy : y ∈ Paper.Transf 2 cIn) :
    1 ≤ Paper.numberOfNewLines y := by
  by_contra hcon
  have hzero : Paper.numberOfNewLines y = 0 := by omega
  have hnn : newline ∉ y := List.count_eq_zero.1 hzero
  have hlen := length_of_mem_transf hy
  have := Paper.length_le_maxLineLength_of_no_newline hnn
  have hbound : Paper.maxLineLength y ≤ 2 := hy.choose_spec.2.2
  omega

private lemma paper_goal_cPaper : Paper.Goal 2 cIn cPaper := by
  refine ⟨⟨cIn, Paper.mem_compacted_self cIn_noDoubleBreak, by decide,
    Paper.maxLineLength_le_of_tails (by decide)⟩, fun y hy => ?_⟩
  rw [show Paper.numberOfNewLines cPaper = 1 from by decide]
  exact one_le_newlines hy

/-- The paper insists on three characters, so it rejects the book's answer. -/
private lemma not_paper_goal_cBook : ¬ Paper.Goal 2 cIn cBook := by
  intro h
  exact absurd (length_of_mem_transf h.1) (by decide)

/-! ## The book's answer -/

private lemma recast_cBook : Book.Recast cIn cBook :=
  Book.recast_of_recast1
    (Book.recast1_dropLeading (b := [blank]) (o := cBook)
      (Book.singleton_mem_break (Or.inl rfl)))

/-- `␣AB` has one word of two letters, so no recast of it is shorter than two
characters. -/
private lemma two_le_length_of_recast {y : Text Char} (h : Book.Recast cIn y) : 2 ≤ y.length := by
  have hb := Book.le_length_of_recast h
  rw [show Book.words cIn = [cBook] from by decide] at hb
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
    List.length_nil] at hb
  have : cBook.length = 2 := by decide
  omega

private lemma book_goal_cBook : Book.Goal 2 cIn cBook :=
  Book.mem_solutions_iff.2
    ⟨⟨Book.mem_minRecasts_iff.2 ⟨recast_cBook, fun _ hy => two_le_length_of_recast hy⟩,
      Book.maxLine_le_of_tails (by decide)⟩,
      fun _ _ _ => by rw [show Book.newLines cBook = 0 from by decide]; exact Nat.zero_le _⟩

/-- The book takes the shortest recast, so it rejects the paper's answer: the
leading break can always be dropped. -/
private lemma not_book_goal_cPaper : ¬ Book.Goal 2 cIn cPaper := by
  intro h
  have hle := (Book.mem_minRecasts_iff.1 (Book.solutions_subset_minRecasts 2 cIn h)).2
    cBook recast_cBook
  have h1 : cPaper.length = 3 := by decide
  have h2 : cBook.length = 2 := by decide
  omega

/-! ## The comparison -/

/-- **The two specifications are not the same relation.**

For the input `␣AB` with a line limit of two characters, each of Meyer's two
specifications produces an output that the other rejects: the 1985 one an empty
first line, the 2022 one no first line at all.

One separating example is enough to show the relations differ, which is all this
states.  Where they differ, and whether they agree elsewhere, is discussed in the
module header and is not proved. -/
example :
    ∃ (M : ℕ) (i o₁ o₂ : Text Char),
      Paper.Goal M i o₁ ∧ ¬ Book.Goal M i o₁ ∧
      Book.Goal M i o₂ ∧ ¬ Paper.Goal M i o₂ :=
  ⟨2, cIn, cPaper, cBook,
    paper_goal_cPaper, not_book_goal_cPaper, book_goal_cBook, not_paper_goal_cBook⟩


end Meyer.Comparison
