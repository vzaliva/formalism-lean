import Meyer.Paper.Facts
import Meyer.Char

/-!
# The paper's example, and an alphabet without letters

`Meyer.Paper` is stated over an abstract alphabet.  This module instantiates it
twice: at `Char`, for Meyer's own example and his nondeterminism claim, which
`decide` settles; and at `Bool`, an alphabet with no letters, to check that the
1985 specification needs none.
-/

namespace Meyer.Paper

/-! ## The specification is nondeterministic

Meyer: "there may be more than one correct output for a given input; in other
words, a truly general specification of the problem should be nondeterministic."

The witness is his own, from his analysis of the ambiguity in Goodenough and
Gerhart's prose: with `MAXPOS = 10` and the input `WHO WHAT WHEN` "there are two
equally correct two-line solutions (`WHAT` may be on either the first or second
line)".  Their specification, he suspects, was nondeterministic by accident;
his is so by design, and the formal `goal` does relate the input to both.

The paper states no assumption on `CHAR` beyond its two distinguished elements,
so the claim is made here at `Char` and not for an abstract alphabet: on an
alphabet without letters the relation is a function, and the claim would
attribute to the paper an assumption it does not make. -/

section Nondeterminism

/-! The example is a text over Lean's `Char`, an alphabet with letters; on an
alphabet without letters the relation is a function. -/

/-- Meyer's input, `WHO WHAT WHEN`. -/
private def wIn : Text Char := "WHO WHAT WHEN".toList

/-- One acceptable output: `WHAT` on the first line. -/
private def wOut₁ : Text Char := "WHO WHAT\nWHEN".toList

/-- The other: `WHAT` on the second line. -/
private def wOut₂ : Text Char := "WHO\nWHAT WHEN".toList

private lemma wIn_noDoubleBreak : NoDoubleBreak wIn := by decide

private lemma wIn_mem_compacted : wIn ∈ Compacted wIn :=
  mem_compacted_self wIn_noDoubleBreak

/-- Anything reachable from the input has its length: `COMPACTED` preserves it
because the input already has single breaks, and `EQUIVALENT` preserves it by
definition. -/
private lemma length_of_mem_transf {y : Text Char} (hy : y ∈ Transf 10 wIn) :
    y.length = 13 := by
  obtain ⟨b, hb, hEquiv, -⟩ := hy
  rw [length_eq_of_mem_equivalent hEquiv, length_eq_of_mem_compacted wIn_noDoubleBreak hb]
  decide

/-- Every acceptable output has at least one newline: without one it would be a
single line of thirteen characters, and `MAXPOS` is ten. -/
private lemma one_le_newlines {y : Text Char} (hy : y ∈ Transf 10 wIn) :
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
private lemma goal_of_one_newline {o : Text Char} (ho : o ∈ Equivalent wIn)
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
    ∃ (n : ℕ) (i o₁ o₂ : Text Char), Goal n i o₁ ∧ Goal n i o₂ ∧ o₁ ≠ o₂ :=
  ⟨10, wIn, wOut₁, wOut₂, goal_wOut₁, goal_wOut₂, by decide⟩

end Nondeterminism

/-! ## An alphabet without letters

`Bool`, with `true` for `blank` and `false` for `new_line`, is an alphabet of the
paper's kind and not of the book's.  Meyer's domain theorem holds there, as it
holds on every alphabet, and says that every text has an output: nothing in the
1985 specification needs a letter to exist.  The instance is local to this
check. -/

section Letterless

local instance : Alphabet Bool := ⟨true, false⟩

example (MAXPOS : ℕ) : DomGoal Bool MAXPOS = Set.univ := by
  rw [domGoal_eq_noOversizeWord]
  ext s
  simp only [Set.mem_univ, iff_true]
  intro t _ hlen
  rcases t with _ | ⟨c, t⟩
  · simp at hlen
  · exact ⟨c, List.mem_cons_self .., by rcases c <;> decide⟩

end Letterless

end Meyer.Paper
