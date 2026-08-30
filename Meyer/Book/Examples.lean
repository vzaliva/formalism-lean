import Meyer.Book.Bug
import Meyer.Char

/-!
# The book's example

`Meyer.Book` is stated over an abstract alphabet; this module instantiates it at
`Char` for Meyer's own worked example, `␣␣ABC␣␣D␣␣EFG` at `M = 5` (p. 176), which
`decide` settles: the two solutions he displays for `T5`, and the third output
that the literal reading of `M3` admits, `Meyer.Book.Bug`.  Both facts are
proved for an abstract alphabet in their own modules; here they are seen on the
text Meyer chose.
-/

namespace Meyer.Book

/-! ## Meyer's example -/

section Example

/-! The example is a text over Lean's `Char`. -/

/-- Meyer's input, `␣␣ABC␣␣D␣␣EFG` (p. 176).

The definitions and lemmas of this section are public because
`Meyer.Book.Bug` reuses them: the defect it exhibits is a third output for this
same input, which the specification as Meyer writes it accepts and the
specification he describes rejects. -/
def exIn : Text Char := "  ABC  D  EFG".toList

/-- His `out`: the break after `D` becomes the line break. -/
def exOut₁ : Text Char := "ABC D\nEFG".toList

/-- His `other`: the break after `ABC` becomes the line break. -/
private def exOut₂ : Text Char := "ABC\nD EFG".toList

private lemma recast_exOut₁ : Recast exIn exOut₁ :=
  recast_trans
    (recast_of_recast1 (recast1_dropLeading (b := [blank, blank])
      (o := "ABC  D  EFG".toList) break_blanks))
    (recast_trans
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC".toList)
        (y := "D  EFG".toList) break_blanks (s := blank) (Or.inl rfl)))
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC D".toList)
        (y := "EFG".toList) break_blanks (s := newline) (Or.inr rfl))))

private lemma recast_exOut₂ : Recast exIn exOut₂ :=
  recast_trans
    (recast_of_recast1 (recast1_dropLeading (b := [blank, blank])
      (o := "ABC  D  EFG".toList) break_blanks))
    (recast_trans
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC".toList)
        (y := "D  EFG".toList) break_blanks (s := newline) (Or.inr rfl)))
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC\nD".toList)
        (y := "EFG".toList) break_blanks (s := blank) (Or.inl rfl))))

/-- `exIn` has three words of seven letters, so no recast of it is shorter than
nine characters. -/
private lemma nine_le_length_of_recast {y : Text Char} (h : Recast exIn y) : 9 ≤ y.length := by
  have hb := le_length_of_recast h
  rw [show words exIn = ["ABC".toList, "D".toList, "EFG".toList] from by decide,
    show (["ABC".toList, "D".toList, "EFG".toList] : List (Text Char)).flatten.length = 7 from
      by decide,
    show (["ABC".toList, "D".toList, "EFG".toList] : List (Text Char)).length = 3 from
      by decide] at hb
  omega

/-- Nine characters is the minimum, so any nine-character recast attains it. -/
lemma mem_minRecasts_of_length_nine {o : Text Char} (ho : Recast exIn o) (h : o.length = 9) :
    o ∈ MinRecasts exIn :=
  mem_minRecasts_iff.2 ⟨ho, fun _ hy => h ▸ nine_le_length_of_recast hy⟩

/-- Nothing acceptable fits on one line: every shortest recast has nine
characters, and `M` is five.  Both readings of `M3` need this. -/
lemma newline_mem_of_mem_minRecasts {y : Text Char} (hy : y ∈ MinRecasts exIn)
    (hmax : maxLine y ≤ 5) : newline ∈ y := by
  by_contra hnn
  have h9 := nine_le_length_of_recast (mem_minRecasts_iff.1 hy).1
  have := length_le_maxLine_of_no_newline hnn
  omega

/-- The same in the form `T5` uses. -/
private lemma one_le_newLines {y : Text Char} (hy : y ∈ MinRecasts exIn)
    (hmax : maxLine y ≤ 5) :
    1 ≤ newLines y :=
  Nat.one_le_iff_ne_zero.2 fun h =>
    List.count_eq_zero.1 h (newline_mem_of_mem_minRecasts hy hmax)

/-- Meyer's `out` is a solution.  `Meyer.Book.Bug` reuses this. -/
lemma goal_exOut₁ : Goal 5 exIn exOut₁ :=
  mem_solutions_iff.2
    ⟨⟨mem_minRecasts_of_length_nine recast_exOut₁ (by decide),
      maxLine_le_of_tails (by decide)⟩,
      fun y hy hmy => by rw [show newLines exOut₁ = 1 from by decide]; exact one_le_newLines hy hmy⟩

private lemma goal_exOut₂ : Goal 5 exIn exOut₂ :=
  mem_solutions_iff.2
    ⟨⟨mem_minRecasts_of_length_nine recast_exOut₂ (by decide),
      maxLine_le_of_tails (by decide)⟩,
      fun y hy hmy => by rw [show newLines exOut₂ = 1 from by decide]; exact one_le_newLines hy hmy⟩

/-- Meyer's witness for `T5`, settled by `decide`. -/
example : ∃ (M : ℕ) (i o₁ o₂ : Text Char), Goal M i o₁ ∧ Goal M i o₂ ∧ o₁ ≠ o₂ :=
  ⟨5, exIn, exOut₁, exOut₂, goal_exOut₁, goal_exOut₂, by decide⟩

end Example

/-! ## The `M3` defect on Meyer's example

His input with a third output, `ABC / D / EFG`. -/

/-- Three lines where two are enough. -/
private def exOut₃ : Text Char := "ABC\nD\nEFG".toList

private lemma recast_exOut₃ : Recast exIn exOut₃ :=
  recast_trans
    (recast_of_recast1 (recast1_dropLeading (b := [blank, blank])
      (o := "ABC  D  EFG".toList) break_blanks))
    (recast_trans
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC".toList)
        (y := "D  EFG".toList) break_blanks (s := newline) (Or.inr rfl)))
      (recast_of_recast1 (recast1_replace (b := [blank, blank]) (x := "ABC\nD".toList)
        (y := "EFG".toList) break_blanks (s := newline) (Or.inr rfl))))

/-- Under the literal `M3`, a three-line output is as good as a two-line one. -/
private lemma goal_exOut₃ : Bug.Goal 5 exIn exOut₃ := by
  refine ⟨⟨mem_minRecasts_of_length_nine recast_exOut₃ (by decide),
    maxLine_le_of_tails (by decide)⟩, fun y hy => ?_⟩
  rw [Bug.newLines_eq, Bug.newLines_eq, if_pos (by decide : newline ∈ exOut₃),
    if_pos (newline_mem_of_mem_minRecasts hy.1 hy.2)]

/-- It is not a solution of the specification Meyer describes: it has two new
lines where `ABC␣D / EFG` has one. -/
private lemma not_goal_exOut₃ : ¬ Meyer.Book.Goal 5 exIn exOut₃ := by
  intro h
  obtain ⟨-, hmin⟩ := mem_solutions_iff.1 h
  obtain ⟨⟨h₁, h₂⟩, -⟩ := mem_solutions_iff.1 goal_exOut₁
  have := hmin exOut₁ h₁ h₂
  rw [show Meyer.Book.newLines exOut₃ = 2 from by decide,
    show Meyer.Book.newLines exOut₁ = 1 from by decide] at this
  omega

/-- **The defect, on Meyer's own example**: the specification as written accepts
`ABC / D / EFG`, and the specification as described does not. -/
example : ∃ (M : ℕ) (i o : Text Char), Bug.Goal M i o ∧ ¬ Goal M i o :=
  ⟨5, exIn, exOut₃, goal_exOut₃, not_goal_exOut₃⟩


end Meyer.Book
