import Meyer.Paper.Spec

/-!
# Basic API for Meyer's specification

Lemmas about the definitions in `Meyer.Paper.Spec` that are not themselves claims of
the paper.  `Meyer.Paper.Retention` and `Meyer.Paper.Facts` use them to establish Meyer's
assertions about the specification.

The main content is the specialisation of `Meyer.Common.maxRun` to newline-free
runs, including a reformulation (`maxLineLength_le_of_tails`) under which
concrete cases fall to `decide`.  The module ends with the two halves of Meyer's
remark that `TRIMMED (b)` is nonempty exactly when `b` has no oversize word.
-/

namespace Meyer.Paper

variable {α : Type*} [Alphabet α]

/-! ## Decidability

The specification is stated with `Prop`-valued predicates, following Meyer.
These instances let concrete cases be settled by `decide`; they add nothing to
the specification's content. -/

instance [DecidableEq α] : DecidableRel (fun x y : α => IsBreak x → ¬ IsBreak y) :=
  fun x y => inferInstanceAs (Decidable (IsBreak x → ¬ IsBreak y))

instance [DecidableEq α] (s : Text α) : Decidable (NoDoubleBreak s) :=
  inferInstanceAs (Decidable (List.IsChain _ s))

instance [DecidableEq α] : DecidableRel (fun x y : α => x = y ∨ (IsBreak x ∧ IsBreak y)) :=
  fun x y => inferInstanceAs (Decidable (x = y ∨ (IsBreak x ∧ IsBreak y)))

instance [DecidableEq α] (b s : Text α) : Decidable (s ∈ Equivalent b) :=
  inferInstanceAs (Decidable (List.Forall₂ _ s b))

/-! ## `maxLineLength`

`Meyer.Common.maxRun` carries the work; these are the specialisations to
newline-free runs, kept under the names the rest of the development uses and in
Meyer's `newline ∉ t` phrasing. -/

private lemma not_mem_iff_forall_ne {t : Text α} :
    newline ∉ t ↔ ∀ c ∈ t, c ≠ newline := by
  simp only [ne_eq]
  exact ⟨fun h c hc hcn => h (hcn ▸ hc), fun h hn => h newline hn rfl⟩

/-- Every newline-free infix is at most as long as the longest line. -/
private lemma le_maxLineLength {s t : Text α} (ht : t.IsInfix s) (hn : newline ∉ t) :
    t.length ≤ maxLineLength s :=
  le_maxRun ht (not_mem_iff_forall_ne.1 hn)

/-- To bound the longest line it suffices to bound every newline-free infix. -/
private lemma maxLineLength_le {s : Text α} {N : ℕ}
    (h : ∀ t : Text α, t.IsInfix s → newline ∉ t → t.length ≤ N) :
    maxLineLength s ≤ N :=
  maxRun_le fun t ht hp => h t ht (not_mem_iff_forall_ne.2 hp)

/-- The form used on concrete texts: the quantification is bounded, so `decide`
can discharge it. -/
lemma maxLineLength_le_of_tails {s : Text α} {N : ℕ}
    (h : ∀ u ∈ s.tails, ∀ t ∈ u.inits, newline ∉ t → t.length ≤ N) :
    maxLineLength s ≤ N :=
  maxRun_le_of_tails fun u hu t ht hp => h u hu t ht (not_mem_iff_forall_ne.2 hp)

/-- A text with no newline at all is one long line. -/
lemma length_le_maxLineLength_of_no_newline {s : Text α} (hn : newline ∉ s) :
    s.length ≤ maxLineLength s :=
  le_maxLineLength (List.infix_refl s) hn

/-! ## `COMPACTED` -/

/-- If a text already has no two adjacent break characters then it is itself a
member of its `SINGLE_BREAKS`, and so nothing in `COMPACTED` can be shorter. -/
private lemma mem_singleBreaks_self {a : Text α} (h : NoDoubleBreak a) :
    a ∈ SingleBreaks a :=
  ⟨List.Sublist.refl a, h⟩

/-- Consequently every member of `COMPACTED (a)` has the full length of `a`:
maximality forces it up, and being a sublist forces it down. -/
lemma length_eq_of_mem_compacted {a b : Text α} (h : NoDoubleBreak a)
    (hb : b ∈ Compacted a) : b.length = a.length :=
  le_antisymm hb.1.1.length_le (hb.2 a (mem_singleBreaks_self h))

/-- A text with no two adjacent break characters is a member of its own
`COMPACTED`: no subsequence of it can be longer than it is. -/
lemma mem_compacted_self {a : Text α} (h : NoDoubleBreak a) : a ∈ Compacted a :=
  ⟨mem_singleBreaks_self h, fun _ hy => hy.1.length_le⟩

/-! ## Words

A *word*, in Meyer's sense, is a "contiguous subsequence of non-break
characters".  `NoOversizeWord` is a bound on the length of the words of a text,
and the results below are more easily stated in those terms than in Meyer's. -/

/-- A text containing no break character: one of Meyer's *words*. -/
def BreakFree (t : Text α) : Prop := ∀ c ∈ t, ¬ IsBreak c

/-- `NoOversizeWord` says exactly that no word is longer than `MAXPOS`.  Meyer's
phrasing quantifies over stretches of the single length `MAXPOS + 1`; the two
agree because any longer word has a word of that length inside it. -/
lemma mem_noOversizeWord_iff (MAXPOS : ℕ) (s : Text α) :
    s ∈ NoOversizeWord α MAXPOS ↔
      ∀ t : Text α, t.IsInfix s → BreakFree t → t.length ≤ MAXPOS := by
  constructor
  · intro h t ht hbf
    by_contra hcon
    obtain ⟨c, hc, hbc⟩ :=
      h (t.take (MAXPOS + 1)) ((List.take_prefix _ t).isInfix.trans ht)
        (by rw [List.length_take]; omega)
    exact hbf c (List.mem_of_mem_take hc) hbc
  · intro h t ht hlen
    by_contra hcon
    have := h t ht fun c hcm hbk => hcon ⟨c, hcm, hbk⟩
    omega

/-! ## `EQUIVALENT` -/

/-- Equivalent texts have the same length; this is the first of Meyer's two
conditions on `EQUIVALENT`, and `List.Forall₂` carries it. -/
lemma length_eq_of_mem_equivalent {b s : Text α} (h : s ∈ Equivalent b) :
    s.length = b.length :=
  List.Forall₂.length_eq h

/-- `Forall₂` splits along an append in its second argument. -/
private lemma forall₂_split {α β : Type*} {R : α → β → Prop} {o : List α} {i₁ i₂ : List β}
    (h : List.Forall₂ R o (i₁ ++ i₂)) :
    ∃ o₁ o₂, o = o₁ ++ o₂ ∧ List.Forall₂ R o₁ i₁ ∧ List.Forall₂ R o₂ i₂ := by
  induction i₁ generalizing o with
  | nil => exact ⟨[], o, rfl, List.Forall₂.nil, h⟩
  | cons a i₁ ih =>
    cases h with
    | cons hab hrest =>
      obtain ⟨o₁, o₂, rfl, h₁, h₂⟩ := ih hrest
      exact ⟨_ :: o₁, o₂, rfl, List.Forall₂.cons hab h₁, h₂⟩

/-- Over a word, an equivalent text is not merely equivalent but equal: break
substitution has nothing to act on. -/
private lemma eq_of_forall₂_of_breakFree {t' t : Text α}
    (h : List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) t' t)
    (hb : BreakFree t) : t' = t := by
  induction h with
  | nil => rfl
  | @cons x y l₁ l₂ hxy _ ih =>
    have hy : ¬ IsBreak y := hb y (List.mem_cons_self ..)
    have hx : x = y := hxy.resolve_right fun hcon => hy hcon.2
    rw [hx, ih fun c hc => hb c (List.mem_cons_of_mem _ hc)]

/-- A word of `b` survives into anything equivalent to `b`. -/
private lemma infix_of_mem_equivalent {b o t : Text α} (ho : o ∈ Equivalent b)
    (ht : t.IsInfix b) (hb : BreakFree t) : t.IsInfix o := by
  obtain ⟨l, r, rfl⟩ := ht
  -- `++` is left-associative, so peel `r` off first, then `t`.
  obtain ⟨o₁, o₄, rfl, h₁, -⟩ := forall₂_split ho
  obtain ⟨o₂, o₃, rfl, -, h₃⟩ := forall₂_split h₁
  exact ⟨o₂, o₄, by rw [eq_of_forall₂_of_breakFree h₃ hb]⟩

/-! ## Nonemptiness

`minSet_nonempty` and `maxSet_nonempty` are in `Meyer.Common`; both
transcriptions need them. -/

/-- `COMPACTED (a)` is never empty: `[]` is always a member of `SINGLE_BREAKS`,
and lengths are bounded by `a`'s.  This is Meyer's "it is trivial to prove that,
given a sequence of characters `a`, there is always at least one sequence `b`
such that relation `short_breaks (a, b)` holds". -/
lemma compacted_nonempty (a : Text α) : (Compacted a).Nonempty := by
  refine maxSet_nonempty _ ⟨[], List.nil_sublist a, by simp [NoDoubleBreak]⟩ ⟨a.length, ?_⟩
  rintro n ⟨y, hy, rfl⟩
  exact hy.1.length_le

/-- Being in the domain is exactly having something reachable: `FEWEST_LINES`
never empties a nonempty set. -/
lemma mem_domGoal_iff [DecidableEq α] (MAXPOS : ℕ) (i : Text α) :
    i ∈ DomGoal α MAXPOS ↔ (Transf MAXPOS i).Nonempty := by
  constructor
  · rintro ⟨o, ho, -⟩
    exact ⟨o, ho⟩
  · intro h
    obtain ⟨o, ho⟩ := minSet_nonempty numberOfNewLines h
    exact ⟨o, ho⟩

/-! ## `TRIMMED`

The two halves of Meyer's observation that "the necessary and sufficient
condition for the existence of at least one sequence `c` such that
`limited_length (b, c)` holds is that `b` contains no word ... of length greater
than `MAXPOS`".  Necessity is `mem_noOversizeWord_of_mem_trimmed`; sufficiency
is `trimmed_nonempty`. -/

/-- If anything is reachable from `b` then `b` has no oversize word: a word of
`b` survives into every equivalent text, where it lies within one line. -/
lemma mem_noOversizeWord_of_mem_trimmed {b c : Text α} {MAXPOS : ℕ}
    (hc : c ∈ Trimmed MAXPOS b) : b ∈ NoOversizeWord α MAXPOS := by
  rw [mem_noOversizeWord_iff]
  intro t ht hbf
  have hn : newline ∉ t := fun hmem => hbf newline hmem (Or.inr rfl)
  exact (le_maxLineLength (infix_of_mem_equivalent hc.1 ht hbf) hn).trans hc.2

/-- The construction behind the converse.  It is not a wrapping algorithm: it
puts every word on a line of its own, which is acceptable precisely when no word
is too long. -/
private def allNewlines [DecidableEq α] (b : Text α) : Text α :=
  b.map fun c => if IsBreak c then newline else c

private lemma mem_equivalent_allNewlines [DecidableEq α] (b : Text α) :
    allNewlines b ∈ Equivalent b := by
  rw [Equivalent, Set.mem_setOf_eq, allNewlines, List.forall₂_map_left_iff,
    List.forall₂_same]
  intro x _
  by_cases hx : IsBreak x
  · exact Or.inr ⟨by simp only [if_pos hx]; exact Or.inr rfl, hx⟩
  · exact Or.inl (by simp only [if_neg hx])

/-- With every break turned into a newline, each line is a single word, so the
longest line is the longest word. -/
private lemma maxLineLength_allNewlines_le [DecidableEq α] {b : Text α} {MAXPOS : ℕ}
    (h : b ∈ NoOversizeWord α MAXPOS) : maxLineLength (allNewlines b) ≤ MAXPOS := by
  refine maxLineLength_le fun t ht hn => ?_
  rw [allNewlines] at ht
  obtain ⟨t', ht', rfl⟩ := List.infix_map_iff.1 ht
  rw [List.length_map]
  exact (mem_noOversizeWord_iff MAXPOS b).1 h t' ht' fun c hc hbc =>
    hn (List.mem_map.2 ⟨c, hc, if_pos hbc⟩)

/-- If no word of `b` is too long then something is reachable from `b`. -/
lemma trimmed_nonempty [DecidableEq α] {b : Text α} {MAXPOS : ℕ}
    (h : b ∈ NoOversizeWord α MAXPOS) :
    (Trimmed MAXPOS b).Nonempty :=
  ⟨allNewlines b, mem_equivalent_allNewlines b, maxLineLength_allNewlines_le h⟩

end Meyer.Paper
