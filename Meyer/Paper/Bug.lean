import Meyer.Paper.Spec

/-!
# Meyer's subsequence definition, read literally

`Meyer/Paper/Spec.lean` transcribes Meyer's specification using `List.Sublist` for
"subsequence", on the grounds that this is plainly what he means.  This module
justifies that choice, by formalising what he actually *writes* and showing it
cannot be what he means.

## The defect

Meyer defines a subsequence of `s` as `s ∘ u`, where `u` is a **sorted** sequence
of natural numbers -- a list of positions, looked up in `s` in order.  Sorted he
defines, in the same box, as

> `∀i ∈ 2..length (s), s (i-1) ≤ s (i)`

with a non-strict `≤`.  So `u` may repeat a position.  Under his own example
`s = <a b a a b d c d>` the index sequence `<3 3 3 3>` is sorted, and therefore
`<a a a a>` is a "subsequence" of `s` -- as is a run of a thousand `a`s.

His description in the main text -- "a sequence made of zero or more of the
elements of `s`, in the same order as in `s`" -- is correct.  It is the formal
definition beside it that admits repetition.

## Why it is fatal rather than untidy

`COMPACTED (a)` is defined as the *longest* members of `SINGLE_BREAKS (a)`.  If
`a` contains any non-break character, repetition supplies members of every
length, so there is no longest one.

Meyer is careful about exactly this.  He says of `MAX_SET` that it "is not always
defined; we have to be careful to apply it only to sets `X` which are finite",
and he discharges the condition where he needs it: "`MAX_SET (X, f)` may be
undefined if `X` is an infinite set.  This cannot occur here, however, since
`SINGLE_BREAKS (a)` is a subset of `SUBSEQUENCES (a)` which, for any sequence of
characters `a`, is finite."

Under the literal reading that last sentence is false for every non-empty `a`:
repeating one position supplies `SUBSEQUENCES (a)` with members of every length.
So the argument Meyer gives for the side condition does not work.

Whether the side condition itself fails is a further question, and the answer
depends on `a`.  `SINGLE_BREAKS (a)` is cut out of `SUBSEQUENCES (a)` by
`NoDoubleBreak`, which forbids two adjacent break characters and so blocks the
repetition of a break.  On an empty or an all-separator input it therefore stays
finite, and `COMPACTED (a)` is defined after all, despite sitting inside an
infinite superset.  It is when `a` contains a character that is *not* a break
that repetition survives the filter, `SINGLE_BREAKS (a)` is unbounded, and
`COMPACTED (a)` falls outside `MAX_SET`'s domain.

`MAX_SET` is partial in the paper and total here: `Meyer.MaxSet` reads "no member
does better", which agrees with Meyer on finite sets, agrees with him on empty
ones (he notes that `MIN_SET` and `MAX_SET` "are defined for empty sets"), and
returns `∅` where he would leave the value undefined.  So what is proved below is
a statement about that completion.  Nothing turns on the choice: undefined and
empty are both fatal, and each contradicts the domain theorem.

That much is already fatal.  Meyer's theorem, proved two pages later, says
`dom (goal)` is exactly the set of texts containing no word longer than `MAXPOS`.
Under the literal reading `dom (goal)` contains only texts made of break
characters, which is `domGoal_subset_breaksOnly` below: no text with a letter in
it has an output, Meyer's own worked example `WHO WHAT WHEN` included
(`Meyer/Paper/Examples.lean`).  For any `MAXPOS ≥ 1` a one-letter text is
therefore a counterexample to his theorem.  Inputs without a letter in them are
untouched, and so is the whole specification at `MAXPOS = 0`, where no text with
a letter in it is claimed to be solvable.  Strictly increasing is therefore
forced, not merely preferable.

## What is and is not claimed

The intended reading is not in conflict with anything; only the literal one is.
The literal reading is strictly the more permissive of the two: every genuine
sublist arises from a strictly increasing index sequence, hence from a
non-decreasing one (`singleBreaks_subset`), so the defect adds junk to
`SINGLE_BREAKS` and removes nothing.  It is the junk that does the damage.
-/

namespace Meyer.Paper.Bug

section

variable {α : Type*} [Alphabet α]

open Meyer.Paper

/-- **Meyer's definition of subsequence, taken literally.**  `t = s ∘ u` for some
sequence `u` of positions that is sorted in his sense, i.e. non-decreasing.

The equation `u.map (s[·]?) = t.map some` says exactly that `u` and `t` have the
same length, every position in `u` is in range, and looking it up in `s` gives
the corresponding element of `t`.  Meyer numbers positions from 1 and Lean from
0, which is immaterial here. -/
def SublistWithRepeats (t s : Text α) : Prop :=
  ∃ u : List ℕ, u.IsChain (· ≤ ·) ∧ u.map (fun i => s[i]?) = t.map some

/-- Repetition really is admitted: three copies of the character at one position
count as a subsequence of that text. -/
example : SublistWithRepeats ['a', 'a', 'a'] ['x', 'a', 'y'] :=
  ⟨[1, 1, 1], by decide, by decide⟩

omit [Alphabet α] in
/-- Every genuine sublist is a subsequence in the literal sense too: it is
`s ∘ u` for a strictly increasing `u`, and strictly increasing is in particular
non-decreasing. -/
private lemma sublistWithRepeats_of_sublist {t s : Text α} (h : t.Sublist s) :
    SublistWithRepeats t s := by
  obtain ⟨u, rfl, hu⟩ := List.sublist_eq_map_getElem h
  refine ⟨u.map Fin.val, (hu.map Fin.val fun _ _ hab => Nat.le_of_lt hab).isChain, ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun i _ => List.getElem?_eq_getElem i.isLt

/-! ## The specification, rebuilt on the literal reading

Only `SINGLE_BREAKS` changes; everything after it is Meyer's, re-stated over the
new definition.  `TRIMMED`, `limited_length`, `FEWEST_LINES` and
`NoOversizeWord` are untouched and are taken from `Meyer`. -/

/-- `SINGLE_BREAKS (a)` under the literal reading. -/
def SingleBreaks (a : Text α) : Set (Text α) :=
  {s | SublistWithRepeats s a ∧ NoDoubleBreak s}

/-- The literal reading only enlarges `SINGLE_BREAKS`. -/
theorem singleBreaks_subset (a : Text α) : Meyer.Paper.SingleBreaks a ⊆ SingleBreaks a :=
  fun _ hs => ⟨sublistWithRepeats_of_sublist hs.1, hs.2⟩

/-- `COMPACTED (a)` under the literal reading. -/
def Compacted (a : Text α) : Set (Text α) :=
  MaxSet (SingleBreaks a) List.length

/-- `short_breaks (a, b)` under the literal reading. -/
def ShortBreaks (a b : Text α) : Prop :=
  b ∈ Compacted a

variable (MAXPOS : ℕ)

/-- `TRANSF (i)` under the literal reading. -/
def Transf (i : Text α) : Set (Text α) :=
  {s | ∃ b, ShortBreaks i b ∧ LimitedLength MAXPOS b s}

/-- `goal (i, o)` under the literal reading. -/
def Goal [DecidableEq α] (i o : Text α) : Prop :=
  o ∈ FewestLines (Transf MAXPOS i)

variable (α) in
/-- `dom (goal)` under the literal reading. -/
def DomGoal [DecidableEq α] : Set (Text α) :=
  {i | ∃ o, Goal MAXPOS i o}

/-! ## The collapse -/

/-- A run of any length of a single non-break character occurring in `a` is a
member of `SINGLE_BREAKS (a)`: it is a subsequence under the literal reading
(repeat that one position), and it contains no break characters at all, so
certainly no two adjacent ones. -/
private lemma replicate_mem_singleBreaks {a : Text α} {p : ℕ} {c : α}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) (n : ℕ) :
    List.replicate n c ∈ SingleBreaks a := by
  constructor
  · refine ⟨List.replicate n p, List.isChain_replicate_of_rel n le_rfl, ?_⟩
    rw [List.map_replicate, List.map_replicate, hp]
  · exact List.isChain_replicate_of_rel n fun h => absurd h hc

/-- **`COMPACTED` collapses.**  If `a` contains a non-break character then
`SINGLE_BREAKS (a)` has members of every length, so no member is longest.

In Meyer's own terms this is the failure of `MAX_SET`'s finiteness side
condition, and `COMPACTED (a)` has no value at all.  `Meyer.MaxSet` totalises
`MAX_SET` as "no member does better", under which the value is `∅`. -/
private lemma compacted_eq_empty {a : Text α} {p : ℕ} {c : α}
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
private lemma transf_eq_empty {a : Text α} {p : ℕ} {c : α}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) :
    Transf MAXPOS a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨b, hb, -⟩
  rw [ShortBreaks, compacted_eq_empty hp hc] at hb
  exact hb

/-- Hence `a` is outside the domain of the specification, however innocuous `a`
is. -/
private lemma not_mem_domGoal [DecidableEq α] {a : Text α} {p : ℕ} {c : α}
    (hp : a[p]? = some c) (hc : ¬ IsBreak c) :
    a ∉ DomGoal α MAXPOS := by
  rintro ⟨o, ho, -⟩
  rw [transf_eq_empty MAXPOS hp hc] at ho
  exact ho

/-- **The specification, read literally, accepts no text with a letter in it.**
`dom (goal)` contains only texts made of break characters.  Meyer's theorem says
it is the set of texts with no word longer than `MAXPOS`, so for any `MAXPOS ≥ 1`
a one-letter text separates the two.  Meyer's own `WHO WHAT WHEN` is among the
casualties: see `Meyer/Paper/Examples.lean`. -/
theorem domGoal_subset_breaksOnly [DecidableEq α] :
    DomGoal α MAXPOS ⊆ {a | ∀ c ∈ a, IsBreak c} := by
  intro a ha c hc
  by_contra hbc
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hc
  exact not_mem_domGoal MAXPOS hp hbc ha

end

end Meyer.Paper.Bug
