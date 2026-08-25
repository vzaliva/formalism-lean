import Meyer.Spec

/-!
# Basic API for Meyer's specification

Lemmas about the definitions in `Meyer.Spec` that are not themselves claims of
the paper.  `Meyer.Facts` uses them to establish Meyer's two assertions about the
specification.

The main content is a workable interface to `maxLineLength`, which is defined as
a supremum over a set and so needs its nonemptiness and boundedness discharged
before anything can be said about it, plus a reformulation
(`maxLineLength_le_of_tails`) under which concrete cases fall to `decide`.
-/

namespace Meyer

/-! ## Decidability

The specification is stated with `Prop`-valued predicates, following Meyer.
These instances let concrete cases be settled by `decide`; they add nothing to
the specification's content. -/

instance : DecidableRel (fun x y : Char => IsBreak x → ¬ IsBreak y) :=
  fun x y => inferInstanceAs (Decidable (IsBreak x → ¬ IsBreak y))

instance (s : Text) : Decidable (NoDoubleBreak s) :=
  inferInstanceAs (Decidable (List.IsChain _ s))

instance : DecidableRel (fun x y : Char => x = y ∨ (IsBreak x ∧ IsBreak y)) :=
  fun x y => inferInstanceAs (Decidable (x = y ∨ (IsBreak x ∧ IsBreak y)))

instance (b s : Text) : Decidable (s ∈ Equivalent b) :=
  inferInstanceAs (Decidable (List.Forall₂ _ s b))

/-! ## Infixes -/

/-- Every infix is a prefix of a suffix, so quantifying over the infixes of a
concrete list is a bounded — and therefore decidable — quantification. -/
private lemma infix_iff_mem_tails_inits {α : Type*} (t s : List α) :
    t.IsInfix s ↔ ∃ u ∈ s.tails, t ∈ u.inits := by
  rw [List.infix_iff_prefix_suffix]
  constructor
  · rintro ⟨u, hpre, hsuf⟩
    exact ⟨u, (List.mem_tails u s).2 hsuf, (List.mem_inits t u).2 hpre⟩
  · rintro ⟨u, hu, ht⟩
    exact ⟨u, (List.mem_inits t u).1 ht, (List.mem_tails u s).1 hu⟩

/-! ## `maxLineLength` -/

/-- The set `maxLineLength` takes the supremum of.  Naming it lets its
nonemptiness and boundedness be discharged once, below, instead of at every
use. -/
private def lineLengths (s : Text) : Set ℕ :=
  {n | ∃ t : Text, t.IsInfix s ∧ newline ∉ t ∧ t.length = n}

/-- `0` is always the length of a newline-free infix, namely `[]`. -/
private lemma lineLengths_nonempty (s : Text) : (lineLengths s).Nonempty :=
  ⟨0, [], List.nil_infix, by simp, rfl⟩

/-- No infix is longer than the list it sits in. -/
private lemma lineLengths_bddAbove (s : Text) : BddAbove (lineLengths s) := by
  refine ⟨s.length, ?_⟩
  rintro n ⟨t, ht, -, rfl⟩
  exact ht.length_le

/-- Every newline-free infix is at most as long as the longest line. -/
lemma le_maxLineLength {s t : Text} (ht : t.IsInfix s) (hn : newline ∉ t) :
    t.length ≤ maxLineLength s :=
  le_csSup (lineLengths_bddAbove s) ⟨t, ht, hn, rfl⟩

/-- To bound the longest line it suffices to bound every newline-free infix. -/
lemma maxLineLength_le {s : Text} {N : ℕ}
    (h : ∀ t : Text, t.IsInfix s → newline ∉ t → t.length ≤ N) :
    maxLineLength s ≤ N := by
  refine csSup_le (lineLengths_nonempty s) ?_
  rintro n ⟨t, ht, hn, rfl⟩
  exact h t ht hn

/-- The form used on concrete texts: the quantification is bounded, so `decide`
can discharge it. -/
lemma maxLineLength_le_of_tails {s : Text} {N : ℕ}
    (h : ∀ u ∈ s.tails, ∀ t ∈ u.inits, newline ∉ t → t.length ≤ N) :
    maxLineLength s ≤ N := by
  refine maxLineLength_le ?_
  intro t ht hn
  obtain ⟨u, hu, htu⟩ := (infix_iff_mem_tails_inits t s).1 ht
  exact h u hu t htu hn

/-- A text with no newline at all is one long line. -/
lemma length_le_maxLineLength_of_no_newline {s : Text} (hn : newline ∉ s) :
    s.length ≤ maxLineLength s :=
  le_maxLineLength (List.infix_refl s) hn

/-! ## `COMPACTED` -/

/-- If a text already has no two adjacent break characters then it is itself a
member of its `SINGLE_BREAKS`, and so nothing in `COMPACTED` can be shorter. -/
private lemma mem_singleBreaks_self {a : Text} (h : NoDoubleBreak a) :
    a ∈ SingleBreaks a :=
  ⟨List.Sublist.refl a, h⟩

/-- Consequently every member of `COMPACTED (a)` has the full length of `a`:
maximality forces it up, and being a sublist forces it down. -/
lemma length_eq_of_mem_compacted {a b : Text} (h : NoDoubleBreak a)
    (hb : b ∈ Compacted a) : b.length = a.length :=
  le_antisymm hb.1.1.length_le (hb.2 a (mem_singleBreaks_self h))

/-- A text with no two adjacent break characters is a member of its own
`COMPACTED`: no subsequence of it can be longer than it is. -/
lemma mem_compacted_self {a : Text} (h : NoDoubleBreak a) : a ∈ Compacted a :=
  ⟨mem_singleBreaks_self h, fun _ hy => hy.1.length_le⟩

/-- When `a` itself has single breaks, `COMPACTED (a)` is exactly `{a}`: any
member is a sublist of `a` of the same length, hence `a`. -/
lemma eq_of_mem_compacted {a b : Text} (h : NoDoubleBreak a) (hb : b ∈ Compacted a) :
    b = a :=
  hb.1.1.eq_of_length (length_eq_of_mem_compacted h hb)

/-! ## `EQUIVALENT` -/

/-- Equivalent texts have the same length; this is the first of Meyer's two
conditions on `EQUIVALENT`, and `List.Forall₂` carries it. -/
lemma length_eq_of_mem_equivalent {b s : Text} (h : s ∈ Equivalent b) :
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

/-- Over a stretch containing no break characters, an equivalent text is not
merely equivalent but equal: break substitution has nothing to act on. -/
private lemma eq_of_forall₂_of_noBreak {t' t : Text}
    (h : List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) t' t)
    (hb : ∀ c ∈ t, ¬ IsBreak c) : t' = t := by
  induction h with
  | nil => rfl
  | @cons x y l₁ l₂ hxy _ ih =>
    have hy : ¬ IsBreak y := hb y (List.mem_cons_self ..)
    have hx : x = y := hxy.resolve_right fun hcon => hy hcon.2
    rw [hx, ih fun c hc => hb c (List.mem_cons_of_mem _ hc)]

/-- A break-free stretch of `b` survives into anything equivalent to `b`. -/
lemma infix_of_mem_equivalent {b o t : Text} (ho : o ∈ Equivalent b)
    (ht : t.IsInfix b) (hb : ∀ c ∈ t, ¬ IsBreak c) : t.IsInfix o := by
  obtain ⟨l, r, rfl⟩ := ht
  -- `++` is left-associative, so peel `r` off first, then `t`.
  obtain ⟨o₁, o₄, rfl, h₁, -⟩ := forall₂_split ho
  obtain ⟨o₂, o₃, rfl, -, h₃⟩ := forall₂_split h₁
  exact ⟨o₂, o₄, by rw [eq_of_forall₂_of_noBreak h₃ hb]⟩

/-! ## Nonemptiness of the extremal sets -/

/-- `MIN_SET` of a nonempty set is nonempty: `ℕ` is well-ordered. -/
private lemma minSet_nonempty {α : Type*} {X : Set α} (f : α → ℕ) (h : X.Nonempty) :
    (MinSet X f).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := Nat.sInf_mem (h.image f)
  exact ⟨x, hx, fun y hy => hfx ▸ Nat.sInf_le ⟨y, hy, rfl⟩⟩

/-- `MAX_SET` of a nonempty, bounded set is nonempty.  Meyer's finiteness side
condition in another form. -/
private lemma maxSet_nonempty {α : Type*} {X : Set α} (f : α → ℕ) (h : X.Nonempty)
    (hb : BddAbove (f '' X)) : (MaxSet X f).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := Nat.sSup_mem (h.image f) hb
  exact ⟨x, hx, fun y hy => hfx ▸ le_csSup hb ⟨y, hy, rfl⟩⟩

/-- `COMPACTED (a)` is never empty: `[]` is always a member of `SINGLE_BREAKS`,
and lengths are bounded by `a`'s. -/
lemma compacted_nonempty (a : Text) : (Compacted a).Nonempty := by
  refine maxSet_nonempty _ ⟨[], (List.nil_sublist a), by simp [NoDoubleBreak]⟩ ⟨a.length, ?_⟩
  rintro n ⟨y, hy, rfl⟩
  exact hy.1.length_le

/-- Being in the domain is exactly having something reachable: `FEWEST_LINES`
never empties a nonempty set. -/
lemma mem_domGoal_iff (MAXPOS : ℕ) (i : Text) :
    i ∈ DomGoal MAXPOS ↔ (Transf MAXPOS i).Nonempty := by
  constructor
  · rintro ⟨o, ho, -⟩
    exact ⟨o, ho⟩
  · intro h
    obtain ⟨o, ho⟩ := minSet_nonempty numberOfNewLines h
    exact ⟨o, ho⟩

/-! ## Turning every break into a newline

The construction behind the `⊇` direction of Meyer's domain theorem.  It is not a
wrapping algorithm: it puts every word on a line of its own, which is acceptable
precisely when no word is too long, and `FEWEST_LINES` then only has to be
nonempty rather than computed. -/

/-- Replace every break character by a newline. -/
private def allNewlines (b : Text) : Text :=
  b.map fun c => if IsBreak c then newline else c

private lemma mem_equivalent_allNewlines (b : Text) : allNewlines b ∈ Equivalent b := by
  rw [Equivalent, Set.mem_setOf_eq, allNewlines, List.forall₂_map_left_iff,
    List.forall₂_same]
  intro x _
  by_cases hx : IsBreak x
  · exact Or.inr ⟨by simp only [if_pos hx]; exact Or.inr rfl, hx⟩
  · exact Or.inl (by simp only [if_neg hx])

/-- An infix of a mapped list comes from an infix of the original. -/
private lemma infix_map_exists {α β : Type*} {f : α → β} {t : List β} {b : List α}
    (h : t.IsInfix (b.map f)) : ∃ t' : List α, t'.IsInfix b ∧ t'.map f = t := by
  obtain ⟨l, r, hlr⟩ := h
  obtain ⟨b₁, b₂, rfl, h₁, -⟩ := List.map_eq_append_iff.1 hlr.symm
  obtain ⟨b₃, b₄, rfl, -, h₄⟩ := List.map_eq_append_iff.1 h₁
  exact ⟨b₄, ⟨b₃, b₂, rfl⟩, h₄⟩

/-- With every break turned into a newline, each line is a single word, so the
longest line is the longest word. -/
private lemma maxLineLength_allNewlines_le {b : Text} {MAXPOS : ℕ}
    (h : b ∈ NoOversizeWord MAXPOS) : maxLineLength (allNewlines b) ≤ MAXPOS := by
  refine maxLineLength_le ?_
  intro t ht hn
  obtain ⟨t', ht', rfl⟩ := infix_map_exists ht
  have hnb : ∀ c ∈ t', ¬ IsBreak c := by
    intro c hc hbc
    refine hn ?_
    have := List.mem_map_of_mem (f := fun c => if IsBreak c then newline else c) hc
    simpa only [if_pos hbc] using this
  rw [List.length_map]
  by_contra hcon
  have hlt : MAXPOS + 1 ≤ t'.length := by omega
  refine absurd (h (t'.take (MAXPOS + 1)) ((List.take_prefix _ t').isInfix.trans ht') ?_) ?_
  · rw [List.length_take]; omega
  · rintro ⟨c, hc, hbc⟩
    exact hnb c (List.mem_of_mem_take hc) hbc

/-- If no word of `b` is too long then something is reachable from `b`. -/
lemma trimmed_nonempty {b : Text} {MAXPOS : ℕ} (h : b ∈ NoOversizeWord MAXPOS) :
    (Trimmed MAXPOS b).Nonempty :=
  ⟨allNewlines b, mem_equivalent_allNewlines b, maxLineLength_allNewlines_le h⟩

end Meyer
