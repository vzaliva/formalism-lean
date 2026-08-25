/-
Copyright (c) 2026 Vadim Zaliva. All rights reserved.
-/
import Meyer.Lemmas

/-!
# Retention: compacting a text does not change its words

The one step Meyer asserts without proof, and the only thing standing between the
specification of `Meyer.Spec` and his theorem on the domain of `goal`.

Meyer's justification is a parenthesis:

> any `b ∈ COMPACTED (a)` must have retained from `a` all non break characters
> (if such a character had been omitted, it could be inserted into `b` and yield
> a longer element of `SINGLE_BREAKS (a)`)

together with the unstated observation that they are retained *contiguously*, so
that the *words* of `b` -- its break-free stretches -- are exactly the words of
`a`.  That is `sameWords_of_mem_compacted` below, and
`mem_noOversizeWord_compacted_iff` is its immediate consequence.

## The proof

Meyer's exchange argument, carried out by induction on the derivation of
`b.Sublist a`.  Each step asks what happened to the leading character of `a`: it
was either dropped, in which case maximality of `b` says reinserting it would be
illegal, or retained.

The naive induction fails in the retained case when the character is a break.
Maximality of `b` in `a` does not hand down maximality of the tail of `b` in the
tail of `a`: for `a = "  x"` the compaction is `b = " x"`, and after keeping the
first blank the residual problem is `"x"` against `" x"`, where `" x"` wins.  The
fix is a second invariant, `MaxAfterBreak`, in force exactly when a break has just
been emitted; there competitors are additionally required not to begin with a
break, which is precisely the constraint the emitted break imposes.  The two
invariants alternate.

The conclusions must be asymmetric too.  The unconstrained invariant controls
prefixes as well as infixes; the constrained one controls only infixes, and the
prefix half genuinely fails under it (for `a = " x"` and `b = "x"`, the word `"x"`
is a prefix of `b` but not of `a`).  This costs nothing, because the prefix half
is consumed only by the non-break retention step, and that step always has the
unconstrained invariant available.
-/

namespace Meyer

/-! ## Words

A *word*, in Meyer's sense, is a stretch of characters none of which is a break.
`NoOversizeWord` is a bound on the length of the words of a text, and the content
of the retention lemma is that compaction leaves the words alone. -/

/-- A text containing no break character: one of Meyer's *words*. -/
def BreakFree (t : Text) : Prop := ∀ c ∈ t, ¬ IsBreak c

/-- A tail of a word is a word. -/
private lemma BreakFree.of_cons {c : Char} {t : Text} (h : BreakFree (c :: t)) : BreakFree t :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A word does not begin with a break character. -/
private lemma BreakFree.head {c : Char} {t : Text} (h : BreakFree (c :: t)) : ¬ IsBreak c :=
  h c (List.mem_cons_self ..)

/-- The text does not begin with a break character; vacuously true of `[]`. -/
private def NoBreakHead : Text → Prop
  | [] => True
  | c :: _ => ¬ IsBreak c

@[simp] private lemma noBreakHead_nil : NoBreakHead [] := trivial

@[simp] private lemma noBreakHead_cons {c : Char} {l : Text} :
    NoBreakHead (c :: l) ↔ ¬ IsBreak c := Iff.rfl

/-! ## `NoDoubleBreak` at a cons

`NoDoubleBreak` is a chain condition, and every use below goes through this one
lemma: it is the chain condition rewritten as a statement about the head. -/

/-- Consing onto a text with single breaks keeps them single exactly when the new
character, if it is a break, is not followed by another. -/
private lemma noDoubleBreak_cons_iff {c : Char} {b : Text} :
    NoDoubleBreak (c :: b) ↔ (IsBreak c → NoBreakHead b) ∧ NoDoubleBreak b := by
  cases b with
  | nil => simp [NoDoubleBreak]
  | cons d l => simp [NoDoubleBreak, List.isChain_cons_cons]

/-- A tail of a text with single breaks has single breaks. -/
private lemma NoDoubleBreak.of_cons {c : Char} {b : Text} (h : NoDoubleBreak (c :: b)) :
    NoDoubleBreak b := (noDoubleBreak_cons_iff.1 h).2

/-! ## Words do not cross a break

The two lemmas that let the induction step past a break character: a word sitting
at the front of `c :: l` with `c` a break must be empty, and a word anywhere
inside `c :: l` must in fact be inside `l`. -/

/-- No nonempty word is a prefix of a text beginning with a break. -/
private lemma breakFree_prefix_cons {c : Char} {l t : Text} (hc : IsBreak c) (ht : BreakFree t) :
    t.IsPrefix (c :: l) ↔ t = [] := by
  constructor
  · intro hp
    cases t with
    | nil => rfl
    | cons e s =>
      exact absurd ((List.cons_prefix_cons.1 hp).1 ▸ hc) ht.head
  · rintro rfl; exact List.nil_prefix

/-- A word inside a text beginning with a break lies wholly beyond that break. -/
private lemma breakFree_infix_cons {c : Char} {l t : Text} (hc : IsBreak c) (ht : BreakFree t) :
    t.IsInfix (c :: l) ↔ t.IsInfix l := by
  rw [List.infix_cons_iff, breakFree_prefix_cons hc ht]
  constructor
  · rintro (rfl | h)
    · exact List.nil_infix
    · exact h
  · exact Or.inr

/-! ## The two invariants and the two conclusions -/

/-- The unconstrained invariant: `b` is a longest element of `SINGLE_BREAKS (a)`.
Uncurried, this is exactly `b ∈ COMPACTED (a)`. -/
private def MaxFree (a b : Text) : Prop :=
  b.Sublist a ∧ NoDoubleBreak b ∧
    ∀ y : Text, y.Sublist a → NoDoubleBreak y → y.length ≤ b.length

/-- The strengthened invariant, in force when the character emitted just before
this point was a break: `b` itself must not begin with a break, and it need only
beat competitors that do not begin with one. -/
private def MaxAfterBreak (a b : Text) : Prop :=
  b.Sublist a ∧ NoDoubleBreak b ∧ NoBreakHead b ∧
    ∀ y : Text, y.Sublist a → NoDoubleBreak y → NoBreakHead y → y.length ≤ b.length

/-- `a` and `b` have the same words: the same break-free stretches occur in
each. -/
def SameWords (a b : Text) : Prop :=
  ∀ t : Text, BreakFree t → (t.IsInfix a ↔ t.IsInfix b)

/-- `a` and `b` begin with the same words. -/
private def SameInitialWords (a b : Text) : Prop :=
  ∀ t : Text, BreakFree t → (t.IsPrefix a ↔ t.IsPrefix b)

/-- Agreement on initial words is stable under consing the same character. -/
private lemma cons_sameInitialWords {a b : Text} {c : Char} (hp : SameInitialWords a b) :
    SameInitialWords (c :: a) (c :: b) := by
  intro t ht
  cases t with
  | nil => simp
  | cons e s =>
    rw [List.cons_prefix_cons, List.cons_prefix_cons]
    exact and_congr_right fun _ => hp s ht.of_cons

/-- Agreement on words is stable under consing the same character, given
agreement on initial words: a word of `c :: a` either starts at `c` or sits
inside `a`. -/
private lemma cons_sameWords {a b : Text} {c : Char} (hi : SameWords a b)
    (hp : SameInitialWords a b) : SameWords (c :: a) (c :: b) := by
  intro t ht
  rw [List.infix_cons_iff, List.infix_cons_iff]
  exact or_congr (cons_sameInitialWords hp t ht) (hi t ht)

/-! ## The exchange argument -/

/-- **Meyer's exchange argument.**  A longest element of `SINGLE_BREAKS (a)` has
the same words as `a`, and -- when no break has just been emitted -- the same
initial words.

The two invariants must be proved together: each retention step switches from one
to the other according to whether the retained character is a break. -/
private lemma sameWords_of_sublist {a b : Text} (h : b.Sublist a) :
    (MaxFree a b → SameWords a b ∧ SameInitialWords a b) ∧
    (MaxAfterBreak a b → SameWords a b) := by
  induction h with
  | slnil => exact ⟨fun _ => ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩, fun _ _ _ => Iff.rfl⟩
  | @cons B A c h ih =>
    -- `c` was dropped.  Reinserting it would give a longer element of
    -- `SINGLE_BREAKS (c :: A)` unless `c` is a break and `B` already begins with
    -- one -- which is Meyer's parenthesis.
    constructor
    · rintro ⟨-, hnd, hmax⟩
      have hkey : ¬ NoDoubleBreak (c :: B) := by
        intro hcb
        have := hmax (c :: B) (h.cons_cons c) hcb
        simp only [List.length_cons] at this
        omega
      rw [noDoubleBreak_cons_iff, not_and_or] at hkey
      have hc : IsBreak c := by
        rcases hkey with hk | hk
        · by_contra hcon; exact hk fun hb => absurd hb hcon
        · exact absurd hnd hk
      have hnbh : ¬ NoBreakHead B := by
        rcases hkey with hk | hk
        · intro hcon; exact hk fun _ => hcon
        · exact absurd hnd hk
      obtain ⟨hi, -⟩ := ih.1 ⟨h, hnd, fun y hy hy2 => hmax y (hy.cons c) hy2⟩
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [breakFree_infix_cons hc ht]; exact hi t ht
      · -- both `c :: A` and `B` begin with a break, so neither has a nonempty
        -- initial word
        rw [breakFree_prefix_cons hc ht]
        constructor
        · rintro rfl; exact List.nil_prefix
        · intro hp
          cases t with
          | nil => rfl
          | cons e s =>
            exfalso
            cases B with
            | nil => simp at hp
            | cons d l =>
              have hd : IsBreak d := not_not.1 (by simpa using hnbh)
              exact ht.head (by rw [(List.cons_prefix_cons.1 hp).1]; exact hd)
    · rintro ⟨-, hnd, hbh, hmax⟩
      have hc : IsBreak c := by
        by_contra hcon
        have := hmax (c :: B) (h.cons_cons c)
          (noDoubleBreak_cons_iff.2 ⟨fun hb => absurd hb hcon, hnd⟩) (by simpa using hcon)
        simp only [List.length_cons] at this
        omega
      have hi := ih.2 ⟨h, hnd, hbh, fun y hy hy2 hy3 => hmax y (hy.cons c) hy2 hy3⟩
      intro t ht
      rw [breakFree_infix_cons hc ht]; exact hi t ht
  | @cons_cons B A c h ih =>
    constructor
    · rintro ⟨-, hnd, hmax⟩
      by_cases hc : IsBreak c
      · -- a break is retained: competitors downstream may no longer begin with a
        -- break, and no word crosses `c` on either side
        have hbh : NoBreakHead B := (noDoubleBreak_cons_iff.1 hnd).1 hc
        have hi := ih.2 ⟨h, hnd.of_cons, hbh, fun y hy hy2 hy3 => by
          have := hmax (c :: y) (hy.cons_cons c)
            (noDoubleBreak_cons_iff.2 ⟨fun _ => hy3, hy2⟩)
          simp only [List.length_cons] at this
          omega⟩
        refine ⟨fun t ht => ?_, fun t ht => ?_⟩
        · rw [breakFree_infix_cons hc ht, breakFree_infix_cons hc ht]; exact hi t ht
        · rw [breakFree_prefix_cons hc ht, breakFree_prefix_cons hc ht]
      · -- a non-break is retained: the invariant is unchanged and both
        -- conclusions cons through
        obtain ⟨hi, hp⟩ := ih.1 ⟨h, hnd.of_cons, fun y hy hy2 => by
          have := hmax (c :: y) (hy.cons_cons c)
            (noDoubleBreak_cons_iff.2 ⟨fun hb => absurd hb hc, hy2⟩)
          simp only [List.length_cons] at this
          omega⟩
        exact ⟨cons_sameWords hi hp, cons_sameInitialWords hp⟩
    · rintro ⟨-, hnd, hbh, hmax⟩
      have hc : ¬ IsBreak c := by simpa using hbh
      obtain ⟨hi, hp⟩ := ih.1 ⟨h, hnd.of_cons, fun y hy hy2 => by
        have := hmax (c :: y) (hy.cons_cons c)
          (noDoubleBreak_cons_iff.2 ⟨fun hb => absurd hb hc, hy2⟩) (by simpa using hc)
        simp only [List.length_cons] at this
        omega⟩
      exact cons_sameWords hi hp

/-- **Meyer's retention claim.**  Every member of `COMPACTED (a)` retains all of
`a`'s non-break characters, contiguously, so it has exactly the words of `a`.

`MaxFree` is `COMPACTED` uncurried, so this is the special case of
`sameWords_of_sublist` that the specification actually uses. -/
theorem sameWords_of_mem_compacted {a b : Text} (hb : b ∈ Compacted a) : SameWords a b :=
  ((sameWords_of_sublist hb.1.1).1
    ⟨hb.1.1, hb.1.2, fun y hy hy2 => hb.2 y ⟨hy, hy2⟩⟩).1

/-! ## `NoOversizeWord` in terms of words -/

/-- `NoOversizeWord` says exactly that no word is longer than `MAXPOS`.  Meyer's
phrasing quantifies over stretches of the single length `MAXPOS + 1`; the two
agree because any longer word has a word of that length inside it. -/
theorem mem_noOversizeWord_iff (MAXPOS : ℕ) (s : Text) :
    s ∈ NoOversizeWord MAXPOS ↔
      ∀ t : Text, t.IsInfix s → BreakFree t → t.length ≤ MAXPOS := by
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

/-! ## The step Meyer does not prove -/

variable (MAXPOS : ℕ)

/-- **The one step Meyer asserts without proof.**  Compacting a text does not
change its words, so a compaction of `a` has an oversize word exactly when `a`
does. -/
theorem mem_noOversizeWord_compacted_iff {a b : Text} (hb : b ∈ Compacted a) :
    b ∈ NoOversizeWord MAXPOS ↔ a ∈ NoOversizeWord MAXPOS := by
  have hw : SameWords a b := sameWords_of_mem_compacted hb
  rw [mem_noOversizeWord_iff, mem_noOversizeWord_iff]
  exact ⟨fun h t ht hbf => h t ((hw t hbf).1 ht) hbf,
         fun h t ht hbf => h t ((hw t hbf).2 ht) hbf⟩

end Meyer
