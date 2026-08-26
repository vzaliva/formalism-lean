import Meyer.Book.Spec

/-!
# The recasting relation

Working material for `Meyer.Book.Facts`: the elementary properties of `recast1`
and its reflexive transitive closure.

Two facts do most of the work later.

* A `recast1` step replaces one non-empty all-separator stretch by another, so by
  `Meyer.Common.maxRun_append_mid` it leaves every *letter-only* run of the text
  where it was.  `maxWord` is therefore invariant along `recast`
  (`maxWord_eq_of_recast`).  `maxLine` is not, and must not be: exchanging a
  space for a new line is exactly how the specification breaks lines.

* The `[R]` case on its own is a congruence -- it may be applied inside any
  context -- which `[L]` and `[T]` are not.  That is what lets every space in a
  text be turned into a new line one at a time (`recast_allNewlines`), the
  construction behind Meyer's feasibility theorem.
-/

namespace Meyer.Book

/-! ## Breaks -/

/-- A single separator is a break. -/
lemma singleton_mem_break {s : Char} (hs : IsSeparator s) : [s] ∈ Break :=
  ⟨by simp, by simpa using hs⟩

/-- A non-empty all-separator text is a break. -/
private lemma mem_break_of_forall {b : Text} (hne : b ≠ [])
    (h : ∀ c ∈ b, IsSeparator c) : b ∈ Break :=
  ⟨hne, h⟩

/-- No character of a break is a letter. -/
private lemma not_isLetter_of_mem_break {b : Text} (hb : b ∈ Break) : ∀ c ∈ b, ¬ IsLetter c :=
  fun c hc hcl => hcl (hb.2 c hc)

/-! ## Introducing single steps -/

/-- `[L]`: removal of a leading break. -/
lemma recast1_dropLeading {b o : Text} (hb : b ∈ Break) : Recast1 (b ++ o) o :=
  ⟨b, hb, Or.inl rfl⟩

/-- `[T]`: removal of a trailing break. -/
lemma recast1_dropTrailing {b o : Text} (hb : b ∈ Break) : Recast1 (o ++ b) o :=
  ⟨b, hb, Or.inr (Or.inl rfl)⟩

/-- `[R]`: replacement of a break by a single separator. -/
lemma recast1_replace {b x y : Text} (hb : b ∈ Break) {s : Char} (hs : IsSeparator s) :
    Recast1 (x ++ b ++ y) (x ++ [s] ++ y) :=
  ⟨b, hb, Or.inr (Or.inr ⟨s, hs, x, y, rfl, rfl⟩)⟩

/-- A text beginning with a separator can lose it. -/
lemma recast1_cons {c : Char} (hc : IsSeparator c) (t : Text) : Recast1 (c :: t) t := by
  simpa using recast1_dropLeading (o := t) (singleton_mem_break hc)

/-- Every text recasts to itself. -/
lemma recast_refl (t : Text) : Recast t t := Relation.ReflTransGen.refl

/-- Recasting is transitive. -/
lemma recast_trans {a b c : Text} (h₁ : Recast a b) (h₂ : Recast b c) : Recast a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-- One step is a recast. -/
lemma recast_of_recast1 {a b : Text} (h : Recast1 a b) : Recast a b :=
  Relation.ReflTransGen.single h

/-! ## The termination remark of p. 173 -/

/-- **Meyer's termination argument does not hold.**  Having noted that a naive
implementation would compute `recast1` by brute force, he writes: "If we take
care of applying `[R]`, in the case of a single-separator break, only to replace
it with a **different** separator (otherwise `[R]` is useless since it changes
nothing), each application of `recast1` will either reduce the length or produce
a different text of the same length, so the process will terminate."

Producing a *different* text of the same length does not preclude returning to a
text already visited.  A space rewrites to a new line and a new line back to a
space, both by `[R]` on a single-separator break with a different separator, so
the rewriting can cycle between two texts of length one for ever.  The set of
reachable texts is finite, which bounds a search that records where it has been;
it does not make arbitrary rewriting terminate.

The remark is about a hypothetical implementation rather than about the
specification, and nothing in the chapter depends on it. -/
theorem recast1_cycle : ∃ a b : Text, a ≠ b ∧ Recast1 a b ∧ Recast1 b a :=
  ⟨[blank], [newline], by decide,
    recast1_replace (b := [blank]) (x := []) (y := [])
      (singleton_mem_break (Or.inl rfl)) (s := newline) (Or.inr rfl),
    recast1_replace (b := [newline]) (x := []) (y := [])
      (singleton_mem_break (Or.inr rfl)) (s := blank) (Or.inl rfl)⟩

/-! ## `T1`: recasting does not lengthen -/

/-- A break has at least one character. -/
private lemma one_le_length_of_mem_break {b : Text} (hb : b ∈ Break) : 1 ≤ b.length :=
  Nat.one_le_iff_ne_zero.2 fun h => hb.1 (List.eq_nil_of_length_eq_zero h)

private lemma length_le_of_recast1 {i o : Text} (h : Recast1 i o) : o.length ≤ i.length := by
  obtain ⟨b, hb, h⟩ := h
  have h1 := one_le_length_of_mem_break hb
  rcases h with rfl | rfl | ⟨s, -, x, y, rfl, rfl⟩ <;>
    simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

/-- **`T1`**: `out.count ≤ in.count`.

Meyer: "`[L]` and `[R]` reduce the size of `in`, and `[S]` either reduces it too
... or keeps it constant".  (His `[L]`, `[R]`, `[S]` here are the box's `[L]`,
`[T]`, `[R]`; the labels drift.) -/
theorem length_le_of_recast {i o : Text} (h : Recast i o) : o.length ≤ i.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact (length_le_of_recast1 hstep).trans ih

/-! ## Letter-only runs survive a recast -/

/-- A `recast1` step swaps one all-separator stretch for another, so it leaves
untouched the longest run of characters satisfying any predicate that no
separator satisfies. -/
private lemma maxRun_eq_of_recast1 {p : Char → Prop} (hp : ∀ c, IsSeparator c → ¬ p c)
    {i o : Text} (h : Recast1 i o) : maxRun p i = maxRun p o := by
  obtain ⟨b, hb, h⟩ := h
  have hbp : ∀ c ∈ b, ¬ p c := fun c hc => hp c (hb.2 c hc)
  rcases h with rfl | rfl | ⟨s, hs, x, y, rfl, rfl⟩
  · rw [show b ++ o = [] ++ b ++ o by simp, maxRun_append_mid hb.1 hbp]
    simp
  · rw [show o ++ b = o ++ b ++ [] by simp, maxRun_append_mid hb.1 hbp]
    simp
  · rw [maxRun_append_mid hb.1 hbp,
      maxRun_append_mid (List.cons_ne_nil s []) (by simpa using hp s hs)]

/-- The same, along a whole recast. -/
private lemma maxRun_eq_of_recast {p : Char → Prop} (hp : ∀ c, IsSeparator c → ¬ p c)
    {i o : Text} (h : Recast i o) : maxRun p i = maxRun p o := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (maxRun_eq_of_recast1 hp hstep)

/-- **The longest word is a recast invariant.**  This is `T3` in the form the
feasibility theorem uses; the statement Meyer gives, `WORDS (out) = WORDS (in)`,
is `Meyer.Book.words_eq_of_recast`. -/
lemma maxWord_eq_of_recast {i o : Text} (h : Recast i o) : maxWord i = maxWord o :=
  maxRun_eq_of_recast (fun _ hc hl => hl hc) h

/-! ## Turning every space into a new line

The `[R]` case of `recast1`, unlike the other two, may be applied inside a
context: prefixing both sides of `in = x + b + y`, `out = x + [s] + y` with the
same text gives another instance of `[R]`.  Rewriting one separator at a time is
therefore a recast, which is the construction Meyer calls `owpl`, "one word per
line". -/

/-- The `[R]` case of `recast1` on its own. -/
private def Recast1R (i o : Text) : Prop :=
  ∃ b ∈ Break, ∃ s, IsSeparator s ∧ ∃ x y : Text, i = x ++ b ++ y ∧ o = x ++ [s] ++ y

private lemma recast1_of_recast1R {i o : Text} (h : Recast1R i o) : Recast1 i o := by
  obtain ⟨b, hb, s, hs, x, y, hi, ho⟩ := h
  exact ⟨b, hb, Or.inr (Or.inr ⟨s, hs, x, y, hi, ho⟩)⟩

private lemma recast1R_cons {c : Char} {i o : Text} (h : Recast1R i o) :
    Recast1R (c :: i) (c :: o) := by
  obtain ⟨b, hb, s, hs, x, y, rfl, rfl⟩ := h
  exact ⟨b, hb, s, hs, c :: x, y, by simp, by simp⟩

private lemma recastR_cons {c : Char} {i o : Text}
    (h : Relation.ReflTransGen Recast1R i o) :
    Relation.ReflTransGen Recast1R (c :: i) (c :: o) :=
  Relation.ReflTransGen.lift (c :: ·) (fun _ _ h => recast1R_cons h) h

/-- Meyer's `owpl`, "one word per line": every space becomes a new line, so that
each word ends up on a line of its own. -/
def allNewlines (t : Text) : Text :=
  t.map fun c => if c = blank then newline else c

/-- Exchanging separators does not change a length. -/
@[simp] lemma length_allNewlines (t : Text) : (allNewlines t).length = t.length :=
  List.length_map ..

/-- There are no spaces left. -/
lemma blank_not_mem_allNewlines (t : Text) : blank ∉ allNewlines t := by
  simp only [allNewlines, List.mem_map, not_exists]
  rintro c ⟨-, hc⟩
  by_cases h : c = blank
  · rw [if_pos h] at hc; exact blank_ne_newline hc.symm
  · rw [if_neg h] at hc; exact h hc

private lemma recastR_allNewlines (t : Text) :
    Relation.ReflTransGen Recast1R t (allNewlines t) := by
  induction t with
  | nil => exact Relation.ReflTransGen.refl
  | cons c t ih =>
    by_cases hc : c = blank
    · subst hc
      refine Relation.ReflTransGen.head ?_ (recastR_cons ih)
      exact ⟨[blank], singleton_mem_break (Or.inl rfl), newline, Or.inr rfl, [], t,
        by simp, by simp⟩
    · simpa [allNewlines, hc] using recastR_cons (c := c) ih

/-- **Every text recasts to its one-word-per-line form.** -/
lemma recast_allNewlines (t : Text) : Recast t (allNewlines t) :=
  Relation.ReflTransGen.mono (fun _ _ h => recast1_of_recast1R h) (recastR_allNewlines t)

/-- With no space left in it, a line is a word: the longest line and the longest
word coincide.  This is where the feasibility theorem gets its witness. -/
lemma maxLine_eq_maxWord_of_no_blank {t : Text} (h : blank ∉ t) : maxLine t = maxWord t := by
  refine maxRun_congr_of_mem fun c hc => ?_
  constructor
  · intro hcn hcs
    rcases hcs with rfl | rfl
    · exact h hc
    · exact hcn rfl
  · intro hcl hcn
    exact hcl (Or.inr hcn)

end Meyer.Book
