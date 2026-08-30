import Mathlib.Data.List.Infix
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Lattice

/-!
# Shared vocabulary

Meyer specified the text-formatting problem twice: in *On Formalism in
Specifications* (IEEE Software, 1985), transcribed in `Meyer.Paper`, and again
in chapter 9 of the *Handbook of Requirements and Business Analysis*
(Springer, 2022), transcribed in `Meyer.Book`.  The two derivations share almost
no notation, but they are built from the same three notions:

* texts over a character set with two distinguished characters, `blank` (the
  book's `space`) and `newline`;
* the elements of a set at which a numerical measure is extremal -- the paper's
  `MAX_SET` and `MIN_SET`, the book's `mu` operator;
* the length of the longest run of consecutive characters all satisfying some
  predicate.

They are collected here so that the two transcriptions can be compared rather
than merely placed side by side.

`maxRun` is the one name in this development that is in neither text.  It is the
common generalisation of the paper's `max_line_length` and the book's `maxline`
(M5), `maxword` (M4) and M6; having it lets the book's claim that M5 and M6
define the same function (`Meyer.Book.maxLine_eq_maxRun_letter_or_blank`) be
proved rather than asserted.
-/

namespace Meyer

/-! ## Alphabets and texts

Neither text fixes the character set.  The paper: "the only property of `CHAR`
that matters here is that `CHAR` contains two elements of particular interest,
`blank` and `new_line`".  The book: `CHARACTER ≜ LETTER ∪ SEPARATOR` with
`SEPARATOR ≜ {space, new_line}`, `LETTER ≠ ∅` and `LETTER ∩ SEPARATOR = ∅`
(p. 172).  The two assumptions differ, and each is a typeclass here: `Alphabet`
is the paper's, `Lettered` the book's, and every alphabet of the book's kind is
one of the paper's.  Neither text says that `blank` and `new_line` differ, so
neither class does; the results that need it say so.

`Char` is an instance of both, in `Meyer.Char`; the transcriptions never use it.
Equality of characters is assumed decidable, `[DecidableEq α]`, wherever a
definition or a proof tests it.  That is a Lean-side assumption with no
counterpart in the texts, whose mathematics is classical, and it costs no
generality: every type has a classical instance.  It is kept separate from the
classes so that `decide` runs on the concrete alphabet `Char`. -/

/-- The paper's `CHAR`: a type with two distinguished elements, the paper's
`blank` and `new_line`, the book's `space` and `new_line`. -/
class Alphabet (α : Type*) where
  /-- The paper's `blank`; the book's `space`. -/
  blank : α
  /-- `new_line`, in both texts. -/
  newline : α

export Alphabet (blank newline)

/-- The paper's `seq [CHAR]` and the book's `TEXT`. -/
abbrev Text (α : Type*) := List α

variable {α : Type*} [Alphabet α]

/-- The paper's `BREAK_CHAR ≜ {blank, new_line}`; the book's
`SEPARATOR ≜ {space, new_line}`.

The two texts differ over the word *break*: in the paper a break is a single
character, in the book (`BREAK ≜ SEPARATOR⁺`) it is a non-empty sequence of
them.  The book's sense is `Meyer.Book.Break`. -/
def IsBreak (c : α) : Prop := c = blank ∨ c = newline

instance [DecidableEq α] : DecidablePred (IsBreak (α := α)) :=
  fun c => inferInstanceAs (Decidable (c = blank ∨ c = newline))

/-- The book's `CHARACTER`: an alphabet with at least one letter, `LETTER ≠ ∅`.
`LETTER ∩ SEPARATOR = ∅` and `CHARACTER ≜ LETTER ∪ SEPARATOR` make `LETTER` the
complement of `SEPARATOR`, so a letter is a character that is not a break and
the class has nothing further to say.  It is assumed exactly where a letter is
used: the book's `T5` and the paper's subsequence defect. -/
class Lettered (α : Type*) extends Alphabet α where
  /-- `LETTER ≠ ∅`. -/
  exists_letter : ∃ c : α, ¬ IsBreak c

/-! ## Specifications -/

/-- A specification: a relation between input and output.  The paper (1985):
"a program may be viewed as the implementation of a certain function (`sol`)
which must ensure that a certain relation (`goal`) is satisfied between its
argument and its result".  The paper's `goal`, the book's `S1` read as a
relation, and both specifications in `Native` have this type. -/
abbrev Spec (α : Type*) := Text α → Text α → Prop

/-! ## Extremal subsets

The paper's `MAX_SET (X, f)` and `MIN_SET (X, f)`.  Meyer stresses that these
yield a *subset* of `X` rather than a single element, "since there may be more
than one element with minimum or maximum `f` value" -- the source of the
specification's nondeterminism.  The book's `mu` operator (M1) is `MinSet`
applied to a subset carved out by a condition; see `Meyer.Book.Mu`. -/

/-- `MAX_SET (X, f)`: the elements of `X` at which `f` attains its maximum. -/
def MaxSet {α : Type*} (X : Set α) (f : α → ℕ) : Set α :=
  {x ∈ X | ∀ y ∈ X, f y ≤ f x}

/-- `MIN_SET (X, f)`: the elements of `X` at which `f` attains its minimum. -/
def MinSet {α : Type*} (X : Set α) (f : α → ℕ) : Set α :=
  {x ∈ X | ∀ y ∈ X, f x ≤ f y}

/-- `MIN_SET` of a nonempty set is nonempty: `ℕ` is well-ordered.

This is the book's "minimization lemma" (9.5.6, exercise 9-E.5) in the half that
gets used.  Meyer states it with `A` finite; over `ℕ` no finiteness is needed for
the minimum, only for the maximum. -/
lemma minSet_nonempty {α : Type*} {X : Set α} (f : α → ℕ) (h : X.Nonempty) :
    (MinSet X f).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := Nat.sInf_mem (h.image f)
  exact ⟨x, hx, fun y hy => hfx ▸ Nat.sInf_le ⟨y, hy, rfl⟩⟩

/-- The minimisation is nonempty exactly when there was something to minimise
over.  With `MinSet` this is the whole of the book's "minimization lemma". -/
lemma minSet_nonempty_iff {α : Type*} {X : Set α} (f : α → ℕ) :
    (MinSet X f).Nonempty ↔ X.Nonempty :=
  ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, minSet_nonempty f⟩

/-- `MAX_SET` of a nonempty set whose image is bounded above is nonempty.  Over
`ℕ` boundedness is what the maximum actually needs; Meyer's finiteness side
condition implies it and is strictly stronger. -/
lemma maxSet_nonempty {α : Type*} {X : Set α} (f : α → ℕ) (h : X.Nonempty)
    (hb : BddAbove (f '' X)) : (MaxSet X f).Nonempty := by
  obtain ⟨x, hx, hfx⟩ := Nat.sSup_mem (h.image f) hb
  exact ⟨x, hx, fun y hy => hfx ▸ le_csSup hb ⟨y, hy, rfl⟩⟩

/-! ## Infixes

A "contiguous subsequence" in the paper, a member of `SUBSEQ` in the book
(9.2.6: "`u` is a subsequence of `s` if and only if `s = t + u + v` for some
sequences `t` and `v`"), and `List.IsInfix` here. -/

/-- Every infix is a prefix of a suffix, so quantifying over the infixes of a
concrete list is a bounded, and therefore decidable, quantification. -/
private lemma infix_iff_mem_tails_inits {α : Type*} (t s : List α) :
    t.IsInfix s ↔ ∃ u ∈ s.tails, t ∈ u.inits := by
  simp only [List.infix_iff_prefix_suffix, List.mem_tails, List.mem_inits]
  exact exists_congr fun _ => and_comm

/-- A prefix that avoids a character stops short of it. -/
private lemma prefix_of_prefix_append_cons {α : Type*} {p : α → Prop} {t x y : List α} {c : α}
    (ht : t.IsPrefix (x ++ c :: y)) (htp : ∀ a ∈ t, p a) (hc : ¬ p c) : t.IsPrefix x := by
  induction x generalizing t with
  | nil =>
    cases t with
    | nil => exact List.nil_prefix
    | cons d t' =>
      exact absurd (htp d (List.mem_cons_self ..))
        ((List.cons_prefix_cons.1 ht).1 ▸ hc)
  | cons a x' ih =>
    cases t with
    | nil => exact List.nil_prefix
    | cons d t' =>
      obtain ⟨rfl, ht'⟩ := List.cons_prefix_cons.1 ht
      exact List.cons_prefix_cons.2
        ⟨rfl, ih ht' fun b hb => htp b (List.mem_cons_of_mem _ hb)⟩

/-- A run that avoids `c` cannot cross it. -/
private lemma infix_or_infix_of_infix_append_cons {α : Type*} {p : α → Prop} {t y : List α}
    {c : α} (hc : ¬ p c) (htp : ∀ a ∈ t, p a) :
    ∀ x : List α, t.IsInfix (x ++ c :: y) → t.IsInfix x ∨ t.IsInfix y := by
  intro x
  induction x with
  | nil =>
    intro ht
    rw [List.nil_append, List.infix_cons_iff] at ht
    rcases ht with h | h
    · exact Or.inl (by
        simpa using (prefix_of_prefix_append_cons (x := []) (by simpa using h) htp hc).isInfix)
    · exact Or.inr h
  | cons a x' ih =>
    intro ht
    rw [show (a :: x') ++ c :: y = a :: (x' ++ c :: y) by simp, List.infix_cons_iff] at ht
    rcases ht with h | h
    · exact Or.inl (prefix_of_prefix_append_cons
        (x := a :: x') (by simpa using h) htp hc).isInfix
    · exact (ih h).imp (fun h' => h'.trans (List.infix_cons (List.infix_refl x'))) id

/-- **The separating lemma.**  A run that avoids the characters of `z` cannot
straddle `z`, so it lies wholly to one side.  Every step of the book's `recast1`
replaces one non-empty all-separator stretch by another, and this is what makes
the letter-only and newline-free runs of a text survive such a step. -/
private lemma infix_or_infix_of_infix_append {α : Type*} {p : α → Prop} {t y : List α}
    (htp : ∀ a ∈ t, p a) :
    ∀ z x : List α, z ≠ [] → (∀ a ∈ z, ¬ p a) → t.IsInfix (x ++ z ++ y) →
      t.IsInfix x ∨ t.IsInfix y := by
  intro z
  induction z with
  | nil => intro _ h; exact absurd rfl h
  | cons c z' ih =>
    intro x _ hzp ht
    rw [show x ++ (c :: z') ++ y = x ++ c :: (z' ++ y) by simp] at ht
    rcases infix_or_infix_of_infix_append_cons (hzp c (List.mem_cons_self ..)) htp x ht with h | h
    · exact Or.inl h
    · rcases z' with _ | ⟨d, z''⟩
      · exact Or.inr (by simpa using h)
      · refine (ih [] (by simp) (fun a ha => hzp a (List.mem_cons_of_mem _ ha))
          (by simpa using h)).imp (fun h' => ?_) id
        exact List.eq_nil_of_infix_nil h' ▸ List.nil_infix

/-! ## Longest runs -/

/-- The length of the longest stretch of consecutive characters of `s` all
satisfying `p`.

The set is nonempty (`[]` is such a stretch, of length `0`) and bounded above by
`s.length`, so the supremum is a maximum.  Meyer takes visible care over exactly
this point in the paper (the box "The reasoning behind formal specifications"):
his `LINE_LENGTHS` is arranged so that it always contains `0`, "even if `s` is an
empty sequence". -/
noncomputable def maxRun {α : Type*} (p : α → Prop) (s : List α) : ℕ :=
  sSup {n | ∃ t : List α, t.IsInfix s ∧ (∀ c ∈ t, p c) ∧ t.length = n}

variable {α : Type*} {p q : α → Prop} {s : List α}

private lemma runLengths_nonempty (p : α → Prop) (s : List α) :
    {n | ∃ t : List α, t.IsInfix s ∧ (∀ c ∈ t, p c) ∧ t.length = n}.Nonempty :=
  ⟨0, [], List.nil_infix, by simp, rfl⟩

private lemma runLengths_bddAbove (p : α → Prop) (s : List α) :
    BddAbove {n | ∃ t : List α, t.IsInfix s ∧ (∀ c ∈ t, p c) ∧ t.length = n} := by
  refine ⟨s.length, ?_⟩
  rintro n ⟨t, ht, -, rfl⟩
  exact ht.length_le

/-- Every run is at most as long as the longest one. -/
lemma le_maxRun {t : List α} (ht : t.IsInfix s) (hp : ∀ c ∈ t, p c) :
    t.length ≤ maxRun p s :=
  le_csSup (runLengths_bddAbove p s) ⟨t, ht, hp, rfl⟩

/-- To bound the longest run it suffices to bound every run. -/
lemma maxRun_le {N : ℕ} (h : ∀ t : List α, t.IsInfix s → (∀ c ∈ t, p c) → t.length ≤ N) :
    maxRun p s ≤ N := by
  refine csSup_le (runLengths_nonempty p s) ?_
  rintro n ⟨t, ht, hp, rfl⟩
  exact h t ht hp

/-- The form used on concrete texts: the quantification is bounded, so `decide`
can discharge it. -/
lemma maxRun_le_of_tails {N : ℕ}
    (h : ∀ u ∈ s.tails, ∀ t ∈ u.inits, (∀ c ∈ t, p c) → t.length ≤ N) :
    maxRun p s ≤ N := by
  refine maxRun_le fun t ht hp => ?_
  obtain ⟨u, hu, htu⟩ := (infix_iff_mem_tails_inits t s).1 ht
  exact h u hu t htu hp

/-- The empty list has only the empty run. -/
@[simp] lemma maxRun_nil : maxRun p ([] : List α) = 0 :=
  le_antisymm (maxRun_le fun _ ht _ => by simp [List.eq_nil_of_infix_nil ht]) (Nat.zero_le _)

/-- Only the truth value of `p` matters.  This is what the book's remark that M5
and M6 "equivalently" define `maxline` amounts to. -/
lemma maxRun_congr (h : ∀ c, p c ↔ q c) (s : List α) : maxRun p s = maxRun q s := by
  simp only [maxRun, h]

/-- Only the truth value of `p` on the characters actually present matters. -/
lemma maxRun_congr_of_mem (h : ∀ c ∈ s, p c ↔ q c) : maxRun p s = maxRun q s := by
  refine le_antisymm (maxRun_le fun t ht hp => ?_) (maxRun_le fun t ht hq => ?_)
  · exact le_maxRun ht fun c hc => (h c (ht.subset hc)).1 (hp c hc)
  · exact le_maxRun ht fun c hc => (h c (ht.subset hc)).2 (hq c hc)

/-- A weaker predicate has longer runs. -/
lemma maxRun_mono (h : ∀ c, p c → q c) (s : List α) : maxRun p s ≤ maxRun q s :=
  maxRun_le fun _ ht hp => le_maxRun ht fun c hc => h c (hp c hc)

/-- A run of an infix is a run. -/
private lemma maxRun_le_of_infix {s' : List α} (h : s.IsInfix s') : maxRun p s ≤ maxRun p s' :=
  maxRun_le fun _ ht hp => le_maxRun (ht.trans h) hp

/-- **Runs split at a break.**  If `z` is non-empty and none of its characters
satisfies `p`, then no run of `x ++ z ++ y` can cross `z`, so the longest one is
the longer of those on either side.  In particular the value does not depend on
`z` at all: replacing `z` by any other non-empty run of characters failing `p`
leaves it unchanged.

This single lemma discharges all three cases of the book's `recast1` for both
`maxword` and `maxline`. -/
lemma maxRun_append_mid {x z y : List α} (hz : z ≠ []) (hzp : ∀ a ∈ z, ¬ p a) :
    maxRun p (x ++ z ++ y) = max (maxRun p x) (maxRun p y) := by
  refine le_antisymm (maxRun_le fun t ht hp => ?_) (max_le ?_ ?_)
  · rcases infix_or_infix_of_infix_append hp z x hz hzp ht with h | h
    · exact le_max_of_le_left (le_maxRun h hp)
    · exact le_max_of_le_right (le_maxRun h hp)
  · exact maxRun_le_of_infix ⟨[], z ++ y, by simp⟩
  · exact maxRun_le_of_infix ⟨x ++ z, [], by simp⟩

end Meyer
