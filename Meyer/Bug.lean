import Meyer.Spec

/-!
# Meyer's subsequence definition, read literally

`Meyer/Spec.lean` transcribes Meyer's specification using `List.Sublist` for
"subsequence", on the grounds that this is plainly what he means.  This module
justifies that choice, by formalising what he actually *writes* and showing it
cannot be what he means.

## The slip

Meyer defines a subsequence of `s` as `s ∘ u`, where `u` is a **sorted** sequence
of natural numbers -- a list of positions, looked up in `s` in order.  Sorted he
defines, in the same box, as

> `∀i ∈ 2..length (s), s (i-1) ≤ s (i)`

with a non-strict `≤`.  So `u` may repeat a position.  Under his own example
`s = <a b a a b d c d>` the index sequence `<3 3 3 3>` is sorted, and therefore
`<a a a a>` is a "subsequence" of `s` -- as is a run of a thousand `a`s.

His informal gloss in the main text -- "a sequence made of zero or more of the
elements of `s`, in the same order as in `s`" -- is correct.  It is the formal
definition beside it that admits repetition.

## Why it is fatal rather than untidy

`COMPACTED (a)` is defined as the *longest* members of `SINGLE_BREAKS (a)`.  If
`a` contains any non-break character, repetition supplies members of every
length, so there is no longest one and `COMPACTED (a)` is empty.  Everything
downstream is built on it, so `goal` relates nothing to anything.

That contradicts Meyer's own theorem, proved two pages later, that `dom (goal)`
is exactly the set of texts containing no word longer than `MAXPOS`.  Under the
literal reading that theorem is false, which is what
`domGoal_ne_noOversizeWord` below establishes.  Strictly increasing is therefore
forced, not merely preferable.

## What is and is not claimed

The intended reading is not in conflict with anything; only the literal one is.
The literal reading is strictly the more permissive of the two: every genuine
sublist arises from a strictly increasing index sequence, hence from a
non-decreasing one (`singleBreaks_subset`), so the defect adds junk to
`SINGLE_BREAKS` and removes nothing.  It is the junk that does the damage.
-/

namespace Meyer.Bug

open Meyer

/-- **Meyer's definition of subsequence, taken literally.**  `t = s ∘ u` for some
sequence `u` of positions that is sorted in his sense, i.e. non-decreasing.

The equation `u.map (s[·]?) = t.map some` says exactly that `u` and `t` have the
same length, every position in `u` is in range, and looking it up in `s` gives
the corresponding element of `t`.  Meyer numbers positions from 1 and Lean from
0, which is immaterial here. -/
def SublistWithRepeats (t s : Text) : Prop :=
  ∃ u : List ℕ, u.IsChain (· ≤ ·) ∧ u.map (fun i => s[i]?) = t.map some

/-- Repetition really is admitted: three copies of the character at one position
count as a subsequence of that text. -/
example : SublistWithRepeats ['a', 'a', 'a'] ['x', 'a', 'y'] :=
  ⟨[1, 1, 1], by decide, by decide⟩

/-- Every genuine sublist is a subsequence in the literal sense too: it is
`s ∘ u` for a strictly increasing `u`, and strictly increasing is in particular
non-decreasing. -/
lemma sublistWithRepeats_of_sublist {t s : Text} (h : t.Sublist s) : SublistWithRepeats t s := by
  obtain ⟨u, rfl, hu⟩ := List.sublist_eq_map_getElem h
  refine ⟨u.map Fin.val, (hu.map Fin.val fun _ _ hab => Nat.le_of_lt hab).isChain, ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun i _ => List.getElem?_eq_getElem i.isLt

/-! ## The specification, rebuilt on the literal reading

Only `SINGLE_BREAKS` changes; everything after it is Meyer's, re-stated over the
new definition.  `TRIMMED`, `limited_length`, `FEWEST_LINES` and
`NoOversizeWord` are untouched and are taken from `Meyer`. -/

/-- `SINGLE_BREAKS (a)` under the literal reading. -/
def SingleBreaks (a : Text) : Set Text :=
  {s | SublistWithRepeats s a ∧ NoDoubleBreak s}

/-- The literal reading only enlarges `SINGLE_BREAKS`. -/
lemma singleBreaks_subset (a : Text) : Meyer.SingleBreaks a ⊆ SingleBreaks a :=
  fun _ hs => ⟨sublistWithRepeats_of_sublist hs.1, hs.2⟩

/-- `COMPACTED (a)` under the literal reading. -/
def Compacted (a : Text) : Set Text :=
  MaxSet (SingleBreaks a) List.length

/-- `short_breaks (a, b)` under the literal reading. -/
def ShortBreaks (a b : Text) : Prop :=
  b ∈ Compacted a

variable (MAXPOS : ℕ)

/-- `TRANSF (i)` under the literal reading. -/
def Transf (i : Text) : Set Text :=
  {s | ∃ b, ShortBreaks i b ∧ LimitedLength MAXPOS b s}

/-- `goal (i, o)` under the literal reading. -/
def Goal (i o : Text) : Prop :=
  o ∈ FewestLines (Transf MAXPOS i)

/-- `dom (goal)` under the literal reading. -/
def DomGoal : Set Text :=
  {i | ∃ o, Goal MAXPOS i o}

/-! ## The collapse -/

/-- A run of any length of a single non-break character occurring in `a` is a
member of `SINGLE_BREAKS (a)`: it is a subsequence under the literal reading
(repeat that one position), and it contains no break characters at all, so
certainly no two adjacent ones. -/
lemma replicate_mem_singleBreaks {a : Text} {p : ℕ} {c : Char}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) (n : ℕ) :
    List.replicate n c ∈ SingleBreaks a := by
  constructor
  · refine ⟨List.replicate n p, List.isChain_replicate_of_rel n le_rfl, ?_⟩
    rw [List.map_replicate, List.map_replicate, hp]
  · exact List.isChain_replicate_of_rel n fun h => absurd h hc

/-- **`COMPACTED` collapses.**  If `a` contains a non-break character then
`SINGLE_BREAKS (a)` has members of every length, so no member is longest and the
set of longest members is empty. -/
lemma compacted_eq_empty {a : Text} {p : ℕ} {c : Char}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) :
    Compacted a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hmax⟩
  have := hmax _ (replicate_mem_singleBreaks hp hc (x.length + 1))
  rw [List.length_replicate] at this
  omega

/-- With `COMPACTED (a)` empty there is no `b` with `short_breaks (a, b)`, so
nothing is reachable from `a` at all. -/
lemma transf_eq_empty {a : Text} {p : ℕ} {c : Char}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) :
    Transf MAXPOS a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨b, hb, -⟩
  rw [ShortBreaks, compacted_eq_empty hp hc] at hb
  exact hb

/-- Hence `a` is outside the domain of the specification, however innocuous `a`
is. -/
lemma not_mem_domGoal {a : Text} {p : ℕ} {c : Char}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) :
    a ∉ DomGoal MAXPOS := by
  rintro ⟨o, ho, -⟩
  rw [transf_eq_empty MAXPOS hp hc] at ho
  exact ho

/-! ## The conflict

Meyer states, and derives from the definitions, that

> `dom (goal) = {s | ∀i ∈ 1..length (s) − MAXPOS, ∃j ∈ i..i + MAXPOS, s (j) ∈ BREAK_CHAR}`

i.e. that the problem is solvable exactly for texts with no word longer than
`MAXPOS`.  Under the literal reading of "subsequence" that is false. -/

/-- A single letter is a text with no oversize word, for any `MAXPOS ≥ 1`: its
only infixes have length `0` and `1`, and neither is `MAXPOS + 1`. -/
lemma singleton_mem_noOversizeWord (h : 1 ≤ MAXPOS) :
    ['h'] ∈ NoOversizeWord MAXPOS := by
  intro t ht hlen
  have := ht.length_le
  simp only [List.length_cons, List.length_nil] at this
  omega

/-- **Meyer's theorem fails under the literal reading.**  The text `"h"` contains
no word longer than `MAXPOS`, so his characterisation places it in `dom (goal)`;
the literal reading of "subsequence" places it outside.  The two cannot both
stand, and since the characterisation is what he proves, the literal reading is
the one that goes. -/
theorem domGoal_ne_noOversizeWord (h : 1 ≤ MAXPOS) :
    DomGoal MAXPOS ≠ NoOversizeWord MAXPOS := by
  intro hEq
  have hin : ['h'] ∈ NoOversizeWord MAXPOS := singleton_mem_noOversizeWord MAXPOS h
  have hout : ['h'] ∉ DomGoal MAXPOS :=
    not_mem_domGoal MAXPOS (p := 0) (c := 'h') rfl (by decide)
  exact hout (hEq ▸ hin)

end Meyer.Bug
