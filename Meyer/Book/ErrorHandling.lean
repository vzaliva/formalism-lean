import Meyer.Book.Facts

/-!
# Error handling: the variant `S2`

`S1` has a precondition: by `T8` it has a solution exactly when no word of the
input is longer than `M`.  Section 9.5.8, "Error handling" (pp. 179-180), removes
it.  Goodenough and Gerhart required the output to satisfy its properties "up to
the point of an error", and Meyer resolves the ambiguity he finds there by
agreeing "to output as many characters as possible, that is to say, include the
beginning -- the first `M` letters -- of the first offending word".  With
`Prefixes (s)` "the set of all prefixes of `s`", the specification becomes

> `S2   {μu: recast (P) | True, maxline (out) ≤ M | out.count, new_lines (out)}`
> `         where P = {μv: Prefixes ({in}) | maxword (v) ≤ M | –v.count}`

"The only difference is that instead of the recasts of `in` we work with the
recasts of `P`, its longest prefix with no word of length greater than `M`."

## Meyer's claims

On pp. 179-180: "`P` is actually a set, but it is not hard to prove that `P`
consists of at most one element; see exercise 9-E.13, which also requests the
proof that, unlike with theorem `T8` in the previous case, there is now always a
solution.  (In other words: `T8` left open the possibility that the *set* of
solutions could empty; with the present revision you have to prove that it is
never empty, although it might consist of just the empty *text* as its single
element.)"

Exercise 9-E.13 (p. 184): "In the error-handling formal specification (9.5.8),
prove that there is only one maximum-length prefix of `in` with word length of at
most `M` (in the set `P`), and that the resulting output text `out` cannot be
empty."

| claim | where |
|---|---|
| `P` has at most one element | `P_subsingleton` |
| the set of solutions is never empty | `solutions_nonempty` |
| the output text cannot be empty | false: `not_forall_goal_ne_nil` |

## The exercise against p. 180

The second half of the exercise asks for something p. 180 denies.  Read as p. 180
reads it, as a claim about the *set* of solutions, it is `solutions_nonempty`.
Read as written, as a claim about the output *text*, it is false, and for every
`M`: an input of separators only has the empty text as its one output, under `S2`
as under `S1` (`T7`), because such an input has no word at all and so is its own
longest prefix.  That is `not_forall_goal_ne_nil`.

These are the only exceptions once `M` is positive, as the restated "picnic"
version of p. 180 requires ("A positive integer `M`"): the output is then empty
exactly when the input has no letter (`eq_nil_iff_forall_isSeparator`).  At
`M = 0` it is always empty (`solutions_zero`), since the longest prefix with no
word longer than `0` is the leading break.

## How the proofs go

Everything passes through one reduction.  `P` has exactly one element `p`, and
`S2` at `in` is `S1` at `p` (`solutions_eq_of_mem_P`).  `p` has no word longer
than `M`, so `T8` at `p` gives a solution; and when `in` itself has none,
`p = in` and `S2` is `S1` (`solutions_eq_of_maxWord_le`).

## Deviations from the book

* `P` is transcribed with `MaxSet` of the length in place of `μ` with the measure
  `–v.count`.  The measures of this development are natural numbers, in which
  `–v.count` cannot be written, and Meyer offers the alternative himself:
  "Alternatively, one can define a maximization operator."  `MaxSet` is the
  paper's `MAX_SET`, totalised like the rest of the development to return `∅`
  where there is no maximum; that never happens here (`P_nonempty`).

* `Prefixes ({in})` and `recast (P)` apply a function on sequences to a set of
  them, as `S1` does with `recast ({in})`, and are read the same way, as images
  (p. 175: "for a relation `r` over `A` and `B` and a subset `X` of `A`, `r (A)` is
  the image of `A` by `r`").  `Prefixes ({in})` is `Prefixes in`, and `recast (P)`
  is the union of `recast ({p})` over the members `p` of `P`.

* p. 179 sets both `S1` and `S2` in braces, `{μu: ...}`, where p. 175 prints `S1`
  without them.  `μ` already denotes a set, so the braces are read as delimiting
  the formula, not as forming a one-element set of sets.

* As in `S1`, `new_lines` is `M3` as its prose describes it, `Meyer.Book.newLines`,
  not as its formula reads (`Meyer.Book.Bug`).

The names `MinRecasts`, `Solutions` and `Goal` shadow those of `Meyer.Book` on
purpose, as in `Meyer.Book.Bug`.
-/

namespace Meyer.Book.ErrorHandling

open Meyer.Book

variable {α : Type*} [Alphabet α]

/-! ## The specification -/

/-- `Prefixes (s)`: "the set of all prefixes of `s` (which as special cases
includes the empty sequence as well as `s` itself)".  By 9.2.6 a prefix of `s` is
a sequence `t` such that `s = t + u` for some sequence `u`, which is
`List.IsPrefix`. -/
def Prefixes (s : Text α) : Set (Text α) :=
  {t | t <+: s}

/-- **`P`**, "the longest prefix with no word of length greater than `M`":

> `P = {μv: Prefixes ({in}) | maxword (v) ≤ M | –v.count}`

"Since `P` is the result of maximizing the length `v.count`, the formula uses the
`μ` operator to minimize `–v.count`.  Alternatively, one can define a
maximization operator."  That operator is `MaxSet`. -/
def P (M : ℕ) (i : Text α) : Set (Text α) :=
  MaxSet {v ∈ Prefixes i | maxWord v ≤ M} List.length

/-- The first stage of `S2`: the recasts of `P` of minimum length, as
`Meyer.Book.MinRecasts` is the first stage of `S1`.  `recast (P)`, the image of
the set `P` by `recast`, is the union of the images of its members. -/
def MinRecasts (M : ℕ) (i : Text α) : Set (Text α) :=
  Mu (⋃ p ∈ P M i, RecastImage p) (fun _ => True) List.length

/-- **`S2`**, the specification with error handling.

> `{μu: recast (P) | True, maxline (out) ≤ M | out.count, new_lines (out)}`

`S1` with `recast ({in})` replaced by `recast (P)`, and nothing else changed. -/
noncomputable def Solutions [DecidableEq α] (M : ℕ) (i : Text α) : Set (Text α) :=
  Mu (MinRecasts M i) (fun o => maxLine o ≤ M) newLines

/-- The input/output relation `S2` defines. -/
def Goal [DecidableEq α] (M : ℕ) (i o : Text α) : Prop :=
  o ∈ Solutions M i

/-! ## `P`: exercise 9-E.13, first part -/

/-- Membership in `P` unfolded: a prefix of `i` with no word longer than `M`, and
no shorter than any other such prefix. -/
lemma mem_P_iff {M : ℕ} {i p : Text α} :
    p ∈ P M i ↔
      (p <+: i ∧ maxWord p ≤ M) ∧ ∀ v, v <+: i → maxWord v ≤ M → v.length ≤ p.length :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun v hv hmv => h₂ v ⟨hv, hmv⟩⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, fun v hv => h₂ v hv.1 hv.2⟩⟩

/-- **Exercise 9-E.13, first part**: "prove that there is only one maximum-length
prefix of `in` with word length of at most `M` (in the set `P`)"; on p. 179, "`P`
is actually a set, but it is not hard to prove that `P` consists of at most one
element".  Two prefixes of the same text are one a prefix of the other, so two of
the same length are equal. -/
theorem P_subsingleton (M : ℕ) (i : Text α) : (P M i).Subsingleton := by
  intro p hp q hq
  obtain ⟨⟨hpi, hpM⟩, hpmax⟩ := mem_P_iff.1 hp
  obtain ⟨⟨hqi, hqM⟩, hqmax⟩ := mem_P_iff.1 hq
  have hpq : p.length = q.length := le_antisymm (hqmax p hpi hpM) (hpmax q hqi hqM)
  exact (List.prefix_of_prefix_length_le hpi hqi hpq.le).eq_of_length hpq

/-- `P` is not empty: the empty text is a prefix with no word at all, and no prefix
is longer than the text. -/
private lemma P_nonempty (M : ℕ) (i : Text α) : (P M i).Nonempty :=
  maxSet_nonempty _ ⟨[], List.nil_prefix, by simp [maxWord]⟩
    ⟨i.length, by rintro _ ⟨v, hv, rfl⟩; exact hv.1.length_le⟩

/-- So `P` is a one-element set, as Meyer's "its longest prefix" takes it to be. -/
private lemma P_eq_singleton {M : ℕ} {i p : Text α} (hp : p ∈ P M i) : P M i = {p} :=
  (P_subsingleton M i).eq_singleton_of_mem hp

/-! ## The reduction to `S1` -/

/-- **`S2` at `in` is `S1` at `p`**, for `p` the member of `P`.  Everything else
in this module follows from it. -/
lemma solutions_eq_of_mem_P [DecidableEq α] {M : ℕ} {i p : Text α} (hp : p ∈ P M i) :
    Solutions M i = Meyer.Book.Solutions M p := by
  rw [Solutions, MinRecasts, P_eq_singleton hp, Set.biUnion_singleton]
  rfl

/-- A text with no word longer than `M` is its own longest such prefix. -/
private lemma mem_P_self {M : ℕ} {i : Text α} (h : maxWord i ≤ M) : i ∈ P M i :=
  mem_P_iff.2 ⟨⟨List.prefix_refl i, h⟩, fun _ hv _ => hv.length_le⟩

/-- **Where `S1` has a solution, `S2` is `S1`.**  If `maxword (in) ≤ M`, which by
`T8` is exactly when `S1` has a solution, then `P = {in}` and the two
specifications agree. -/
private lemma solutions_eq_of_maxWord_le [DecidableEq α] {M : ℕ} {i : Text α}
    (h : maxWord i ≤ M) : Solutions M i = Meyer.Book.Solutions M i :=
  solutions_eq_of_mem_P (mem_P_self h)

/-! ## There is always a solution: exercise 9-E.13, second part -/

/-- **Exercise 9-E.13, second part, as p. 180 reads it**: "unlike with theorem
`T8` in the previous case, there is now always a solution ... you have to prove
that it is never empty".  `T8` applied at the member of `P`, which has no word
longer than `M`. -/
theorem solutions_nonempty [DecidableEq α] (M : ℕ) (i : Text α) :
    (Solutions M i).Nonempty := by
  obtain ⟨p, hp⟩ := P_nonempty M i
  rw [solutions_eq_of_mem_P hp]
  exact (feasibility M p).2 (mem_P_iff.1 hp).1.2

/-! ## The output text can be empty -/

/-- A text has no word exactly when every character in it is a separator. -/
private lemma maxWord_eq_zero_iff {t : Text α} : maxWord t = 0 ↔ ∀ c ∈ t, IsSeparator c := by
  constructor
  · intro h c hc
    by_contra hl
    have := le_maxRun (p := IsLetter) ((List.singleton_infix_iff c t).2 hc) (by simpa using hl)
    rw [← maxWord, h] at this
    simp at this
  · intro h
    refine Nat.le_zero.1 (maxRun_le fun w hw hl => ?_)
    cases w with
    | nil => exact Nat.le_refl 0
    | cons a w' =>
      exact absurd (h a (hw.subset List.mem_cons_self)) (hl a List.mem_cons_self)

/-- `T7` for `S2`: an input of separators only has the empty text as its one
output.  It has no word, so it is its own longest prefix and `S2` is `S1` on it. -/
private lemma solutions_of_forall_isSeparator [DecidableEq α] {M : ℕ} {i : Text α}
    (h : ∀ c ∈ i, IsSeparator c) : Solutions M i = {[]} := by
  rw [solutions_eq_of_maxWord_le ((maxWord_eq_zero_iff.2 h).trans_le (Nat.zero_le M)),
    Meyer.Book.solutions_of_forall_isSeparator h]

/-- **Exercise 9-E.13, second part, as written, is false**: "the resulting output
text `out` cannot be empty".  For every `M`, positive or not, some input has the
empty text as an output: the one-character input `[space]`, or any other made of
separators only.

p. 180 says as much in the same breath as it points to the exercise: the set of
solutions "might consist of just the empty *text* as its single element".  What
it asks to be proved is `solutions_nonempty`, about the set; what the exercise
asks is about its elements, and fails. -/
theorem not_forall_goal_ne_nil [DecidableEq α] (M : ℕ) :
    ¬ ∀ i o : Text α, Goal M i o → o ≠ [] := fun h =>
  h [blank] [] (by
    rw [Goal, solutions_of_forall_isSeparator (by simp [IsSeparator, IsBreak])]
    exact Set.mem_singleton _) rfl

/-- If the longest prefix has no word in it, it is the whole input, provided
`M ≥ 1`: otherwise one more character would still fit. -/
private lemma eq_of_mem_P_of_maxWord_eq_zero {M : ℕ} (hM : 1 ≤ M) {i p : Text α}
    (hp : p ∈ P M i) (h0 : maxWord p = 0) : p = i := by
  obtain ⟨⟨⟨r, rfl⟩, -⟩, hpmax⟩ := mem_P_iff.1 hp
  cases r with
  | nil => exact (List.append_nil p).symm
  | cons d y =>
    exfalso
    have hsep := maxWord_eq_zero_iff.1 h0
    have hfit : maxWord (p ++ [d]) ≤ 1 := by
      rcases eq_or_ne p [] with rfl | hne
      · exact maxRun_le fun t ht _ => ht.length_le
      · rw [show p ++ [d] = [] ++ p ++ [d] by simp, maxWord,
          maxRun_append_mid hne fun a ha hl => hl (hsep a ha)]
        simpa using maxRun_le (p := IsLetter) (s := [d]) fun t ht _ => ht.length_le
    have := hpmax (p ++ [d]) ⟨y, by simp⟩ (hfit.trans hM)
    simp only [List.length_append, List.length_singleton] at this
    omega

/-- **With `M ≥ 1`, the exceptions are exactly the inputs without a letter.**
The output of `S2` is empty if and only if the input is made of separators only.
`M ≥ 1` is the restated "picnic" version's "A positive integer `M`" (p. 180), and
is needed: see `solutions_zero`. -/
private lemma eq_nil_iff_forall_isSeparator [DecidableEq α] {M : ℕ} (hM : 1 ≤ M)
    {i o : Text α} (ho : Goal M i o) : o = [] ↔ ∀ c ∈ i, IsSeparator c := by
  constructor
  · rintro rfl
    obtain ⟨p, hp⟩ := P_nonempty M i
    have ho' : [] ∈ Meyer.Book.Solutions M p := solutions_eq_of_mem_P hp ▸ ho
    have hrec := (mem_minRecasts_iff.1 (solutions_subset_minRecasts M p ho')).1
    have h0 : maxWord p = 0 := by
      rw [maxWord_eq_of_recast hrec]; simp [maxWord]
    rw [← eq_of_mem_P_of_maxWord_eq_zero hM hp h0]
    exact maxWord_eq_zero_iff.1 h0
  · intro h
    exact Set.mem_singleton_iff.1 (solutions_of_forall_isSeparator h ▸ ho)

/-- At `M = 0` every output is empty: no letter fits on a line, and the longest
prefix with no word is the leading break of the input. -/
private lemma solutions_zero [DecidableEq α] (i : Text α) : Solutions 0 i = {[]} := by
  obtain ⟨p, hp⟩ := P_nonempty 0 i
  rw [solutions_eq_of_mem_P hp, Meyer.Book.solutions_of_forall_isSeparator
    (maxWord_eq_zero_iff.1 (Nat.le_zero.1 (mem_P_iff.1 hp).1.2))]

end Meyer.Book.ErrorHandling
