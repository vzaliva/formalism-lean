import Meyer.Book.Words

/-!
# The book's claims about its specification

Section 9.5 states eight properties of the text-formatting specification,
labelled `T1` to `T8`, and proves or sketches each.  All eight are true.  They
are proved here and in the two preceding modules:

| | claim | where |
|---|---|---|
| `T1` | `out.count ≤ in.count` | `Meyer.Book.length_le_of_recast` |
| `T2` | `maxword (out) ≤ maxline (out)` | `maxWord_le_maxLine` |
| `T3` | `WORDS (out) = WORDS (in)` | `Meyer.Book.words_eq_of_recast` |
| `T4` | `breaks (out).count ≥ breaks (in).count - 2` | `Meyer.Book.length_breaks_ge` |
| `T5` | there can be more than one solution | `goal_not_functional` |
| `T6` | no solution starts or ends with a break | `solution_not_isSeparator_at_ends` |
| `T7` | an all-separator input gives an empty output | `solutions_of_forall_isSeparator` |
| `T8` | a solution exists iff `maxword (in) ≤ M` | `feasibility` |

## The step `T8` passes over

Meyer proves the feasibility theorem `T8` like this.  Assume
`maxword (in) ≤ M`; then

> it suffices to show that the subset `SL` (for "small lines") of `recast ({in})`
> made of elements satisfying `maxline (out) ≤ M` is not empty; we will know then
> by the minimization lemma that a solution (a minimum based on that subset)
> exists.

and he shows `SL` is not empty by exhibiting `owpl`, the text with one word per
line.

`SL` is the wrong set.  `S1` minimises `out.count` **first** and imposes
`maxline (out) ≤ M` afterwards, so the minimisation lemma needs an element of
`SL` that is also of minimum length among all recasts of `in` -- an element of
`MinRecasts i`, not merely of `RecastImage i`.  The theorem is nevertheless true,
and `owpl` is the right witness, but seeing that it is takes two further facts:
that recasting leaves the words of a text alone (`T3`), and that a text is
therefore at least as long as its letters plus one separator between each pair of
consecutive words (`Meyer.Book.length_add_length_words_le`, the content of
exercise 9-E.6).

The proof below avoids the issue rather than repairing it: instead of showing
that a particular witness is of minimum length, it takes an arbitrary element of
`MinRecasts i` -- one exists, because `ℕ` is well-ordered -- and turns each of
its spaces into a new line, which is a recast and changes no length.  The
missing facts are proved anyway, in `Meyer.Book.Words`, because `T3`, `T4` and
`T5` need them.

This is the same last mile as in the 1985 paper, where the corresponding step --
that compacting a text leaves its words alone -- is asserted in a parenthetical
remark; see `Meyer.Paper.Retention`.  In the book's formulation it is much the
easier of the two, because `recast` is a closure and so comes with an induction
principle.
-/

namespace Meyer.Book

variable {α : Type*}

/-! ## Working with the `mu` operator -/

/-- **The minimization lemma** (9.5.6, exercise 9-E.5): `μ a: A | c (a) | m (a)`
"is non empty if and only if at least one element of `A` satisfies `c`".

Meyer states it for finite `A`.  Over `ℕ` finiteness is needed only for a
maximum, and `S1` takes only minima. -/
theorem mu_nonempty_iff {A : Set (Text α)} {c : Text α → Prop} {m : Text α → ℕ} :
    (Mu A c m).Nonempty ↔ ∃ a ∈ A, c a := by
  rw [Mu, minSet_nonempty_iff]
  exact ⟨fun ⟨a, ha, hc⟩ => ⟨a, ha, hc⟩, fun ⟨a, ha, hc⟩ => ⟨a, ha, hc⟩⟩

section Alphabet

variable [Alphabet α]

/-- Membership in the first stage of `S1`: a recast of `i`, no longer than any
other. -/
lemma mem_minRecasts_iff {i o : Text α} :
    o ∈ MinRecasts i ↔ Recast i o ∧ ∀ y, Recast i y → o.length ≤ y.length := by
  constructor
  · rintro ⟨⟨ho, -⟩, hmin⟩
    exact ⟨ho, fun y hy => hmin y ⟨hy, trivial⟩⟩
  · rintro ⟨ho, hmin⟩
    exact ⟨⟨ho, trivial⟩, fun y hy => hmin y hy.1⟩

/-- There is always a shortest recast. -/
lemma minRecasts_nonempty (i : Text α) : (MinRecasts i).Nonempty :=
  minSet_nonempty _ ⟨i, recast_refl i, trivial⟩

/-- Membership in `S1` unfolded. -/
lemma mem_solutions_iff [DecidableEq α] {M : ℕ} {i o : Text α} :
    o ∈ Solutions M i ↔
      (o ∈ MinRecasts i ∧ maxLine o ≤ M) ∧
        ∀ y ∈ MinRecasts i, maxLine y ≤ M → newLines o ≤ newLines y :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun y hy hmy => h₂ y ⟨hy, hmy⟩⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, fun y hy => h₂ y hy.1 hy.2⟩⟩

/-- A solution is in particular a shortest recast. -/
lemma solutions_subset_minRecasts [DecidableEq α] (M : ℕ) (i : Text α) :
    Solutions M i ⊆ MinRecasts i :=
  fun _ ho => ho.1.1

/-! ## Lines -/

/-- The form used on concrete texts: the quantification is bounded, so `decide`
can discharge it. -/
lemma maxLine_le_of_tails {t : Text α} {N : ℕ}
    (h : ∀ u ∈ t.tails, ∀ v ∈ u.inits, newline ∉ v → v.length ≤ N) : maxLine t ≤ N :=
  maxRun_le_of_tails fun u hu v hv hp => h u hu v hv fun hmem => hp newline hmem rfl

/-- A text with no new line in it is one long line. -/
lemma length_le_maxLine_of_no_newline {t : Text α} (h : newline ∉ t) :
    t.length ≤ maxLine t :=
  le_maxRun (List.infix_refl t) fun _ hc hcn => h (hcn ▸ hc)

/-! ## `T2`, and the equivalence of `M5` and `M6` -/

/-- **`T2`**: `maxword (out) ≤ maxline (out)`.  Meyer: "follows directly from
comparing `M4` and `M6`" -- every run of letters is a run of characters other
than `new_line`. -/
theorem maxWord_le_maxLine (t : Text α) : maxWord t ≤ maxLine t :=
  maxRun_mono (fun _ hc hcn => hc (Or.inr hcn)) t

/-- Meyer's remark that `M5` and `M6` define the same function: "Given the
definition of `CHARACTER` we could equivalently define `maxline (in)` as
`max (s.count | s ∈ SUBSEQ (in) ∧ range s ⊆ (LETTER ∪ {space}))`."

It holds because `CHARACTER ≜ LETTER ∪ SEPARATOR` and `SEPARATOR ≜ {space,
new_line}`, both from the box on p. 172, so a character is other than `new_line`
exactly when it is a letter or a space -- provided `space` and `new_line` are
two characters and not one, which neither box says and the remark needs: on an
alphabet where they coincide, `new_line` is a space and `M6` counts it. -/
theorem maxLine_eq_maxRun_letter_or_blank (h : (blank : α) ≠ newline) (t : Text α) :
    maxLine t = maxRun (fun c => IsLetter c ∨ c = blank) t := by
  refine maxRun_congr (fun c => ?_) t
  constructor
  · intro h
    by_cases hb : c = blank
    · exact Or.inr hb
    · exact Or.inl fun hs => hs.elim hb h
  · rintro (hl | rfl)
    · exact fun hcn => hl (Or.inr hcn)
    · exact h

/-- The remark forces `space` and `new_line` to be two characters.  Where they
coincide, the one-character text `[new_line]` has a longest line of length zero
by `M5` and a run of one letter or space by `M6`. -/
theorem blank_ne_newline_of_maxLine_eq
    (h : ∀ t : Text α, maxLine t = maxRun (fun c => IsLetter c ∨ c = blank) t) :
    (blank : α) ≠ newline := by
  intro hbn
  have h₀ : maxLine ([newline] : Text α) ≤ 0 := maxRun_le fun t ht hp => by
    cases t with
    | nil => rfl
    | cons c _ =>
      exact absurd (List.mem_singleton.1 (ht.subset (List.mem_cons_self ..)))
        (hp c (List.mem_cons_self ..))
  have h₁ : ([newline] : Text α).length ≤ maxLine [newline] := h [newline] ▸
    le_maxRun (List.infix_refl _) fun c hc => Or.inr ((List.mem_singleton.1 hc).trans hbn.symm)
  simp at h₁
  omega

/-! ## `T6`: the output has no leading or trailing break

Meyer poses this as one of three questions "unclear from either of the original
specifications", and answers: "For `T6`, the answer is no in this version."  The
reason is that `S1` minimises length before doing anything else, and `[L]` and
`[T]` are always available to remove a leading or trailing break.

The 1985 specification answers the same question the other way: its `COMPACTED`
retains one break character at each end.  See the header of
`Meyer.Book.Spec`. -/

/-- A shortest recast does not begin with a separator: `[L]` would shorten it. -/
lemma head_not_isSeparator {i o : Text α} (ho : o ∈ MinRecasts i) {c : α} {t : Text α}
    (h : o = c :: t) : ¬ IsSeparator c := by
  intro hc
  obtain ⟨hor, homin⟩ := mem_minRecasts_iff.1 ho
  have : o.length ≤ t.length :=
    homin t (recast_trans hor (recast_of_recast1 (h ▸ recast1_cons hc t)))
  rw [h] at this
  simp only [List.length_cons] at this
  omega

/-- Nor does it end with one: `[T]` would shorten it. -/
lemma getLast_not_isSeparator {i o : Text α} (ho : o ∈ MinRecasts i) {t : Text α} {c : α}
    (h : o = t ++ [c]) : ¬ IsSeparator c := by
  intro hc
  obtain ⟨hor, homin⟩ := mem_minRecasts_iff.1 ho
  have hstep : Recast1 o t := h ▸ recast1_dropTrailing (singleton_mem_break hc)
  have : o.length ≤ t.length := homin t (recast_trans hor (recast_of_recast1 hstep))
  rw [h] at this
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- **`T6`**: "Can the output text start or end with a break? ... the answer is no
in this version."  A solution is in particular a shortest recast, and a shortest
recast has no separator at either end -- `[L]` and `[T]` would shorten it. -/
theorem solution_not_isSeparator_at_ends [DecidableEq α] {M : ℕ} {i o : Text α}
    (ho : o ∈ Solutions M i) :
    (∀ (c : α) (t : Text α), o = c :: t → ¬ IsSeparator c) ∧
      (∀ (t : Text α) (c : α), o = t ++ [c] → ¬ IsSeparator c) :=
  ⟨fun _ _ h => head_not_isSeparator (solutions_subset_minRecasts M i ho) h,
    fun _ _ h => getLast_not_isSeparator (solutions_subset_minRecasts M i ho) h⟩

/-! ## `T7`: an input of separators only -/

/-- **`T7`**: "What happens with an input text made of separators only (i.e. of a
single non-empty break)? ... the formal specification yields an empty output."

The 1985 specification answers differently here too, for the reason set out in
`Meyer.Comparison`: its `COMPACTED` keeps one break character, so its output for
an all-separator input is a single space -- which is what Meyer says the
*natural-language* originals "could be construed, although not conclusively" to
do.  That particular input is not formalised; `Meyer.Comparison` proves the two
specifications differ on a closely related one.

`T7` also settles exercise 9-E.13 against itself.  The exercise asks the reader to
prove that the output of the error-handling variant `S2` "cannot be empty", which
p. 180 contradicts in the same breath: the output "might consist of just the empty
`text` as its single element".  For an input of separators only the two agree with
p. 180 and not with the exercise.  `S2` restricts the input to `P`, the longest
prefix whose longest word fits within `M`; an all-separator text has longest word
`0`, so `P` is the whole input and `S2` reduces to `S1` on it.  `T7` then gives the
empty output.  `S2` is formalised in `Meyer.Book.ErrorHandling`, and that last step
is `Meyer.Book.ErrorHandling.not_forall_goal_ne_nil`. -/
theorem solutions_of_forall_isSeparator [DecidableEq α] {M : ℕ} {i : Text α}
    (h : ∀ c ∈ i, IsSeparator c) :
    Solutions M i = {[]} := by
  have hnil : Recast i [] := by
    rcases eq_or_ne i [] with rfl | hne
    · exact recast_refl []
    · exact recast_of_recast1
        (by simpa using recast1_dropLeading (o := ([] : Text α)) ⟨hne, h⟩)
  have hmin : ([] : Text α) ∈ MinRecasts i := mem_minRecasts_iff.2 ⟨hnil, by simp⟩
  ext o
  simp only [Set.mem_singleton_iff]
  constructor
  · intro ho
    have hle := (mem_minRecasts_iff.1 (solutions_subset_minRecasts M i ho)).2 [] hnil
    simpa using hle
  · rintro rfl
    exact ⟨⟨hmin, by simp [maxLine]⟩, fun y _ => by simp [newLines]⟩

/-! ## `T8`: the feasibility theorem -/

/-- **`T8`**: "A solution exists if for an input text `in` and only if
`maxword (in) ≤ M`."

The witness for the "if" half is Meyer's `owpl`, "one word per line", but reached
from the other end: rather than building a short-lined text and arguing that it
is of minimum length, take any shortest recast -- one exists because `ℕ` is
well-ordered -- and turn its spaces into new lines, which is a recast and changes
no length.  Each line of the result is a single word, so the longest line is the
longest word, which recasting has not changed. -/
theorem feasibility [DecidableEq α] (M : ℕ) (i : Text α) :
    (Solutions M i).Nonempty ↔ maxWord i ≤ M := by
  rw [Solutions, mu_nonempty_iff]
  constructor
  · rintro ⟨o, ho, hmax⟩
    rw [maxWord_eq_of_recast (mem_minRecasts_iff.1 ho).1]
    exact (maxWord_le_maxLine o).trans hmax
  · intro h
    obtain ⟨o, ho⟩ := minRecasts_nonempty i
    obtain ⟨hor, homin⟩ := mem_minRecasts_iff.1 ho
    refine ⟨allNewlines o, mem_minRecasts_iff.2
      ⟨recast_trans hor (recast_allNewlines o), fun y hy => ?_⟩, ?_⟩
    · rw [length_allNewlines]
      exact homin y hy
    · rw [maxLine_eq_maxWord_of_forall fun _ hc hn => ne_blank_of_mem_allNewlines hc hn,
        ← maxWord_eq_of_recast (recast_allNewlines o), ← maxWord_eq_of_recast hor]
      exact h

/-- Two spaces are a break. -/
lemma break_blanks : ([blank, blank] : Text α) ∈ Break :=
  ⟨List.cons_ne_nil _ _, by simp [IsSeparator, IsBreak]⟩

end Alphabet

/-! ## `T5`: the specification is nondeterministic

Meyer: "This specification is, in addition, **non-deterministic** ... Did you
notice that the solution given to the example on page 172 was not the only
possible one?  Solution `other` is just as correct as the original `out`."

This is the one theorem of the eight that uses the book's assumption
`LETTER ≠ ∅`, and it needs one more that neither box states: that `space` and
`new_line` are two characters.  With a letter `c` the input `c cc c` at `M = 4`
has the outputs `c cc / c` and `c / cc c`, which differ only in which of the
two separators stands where; on an alphabet without letters every text is a
break and `S1` is a function, and on one where the separators coincide the two
outputs are the same text and `S1` is a function again
(`eq_of_goal_of_blank_eq_newline`, below).

Meyer's own witness, `␣␣ABC␣␣D␣␣EFG` at `M = 5` (p. 176), which the
specification relates both to `ABC␣D / EFG` and to `ABC / D␣EFG`, is a text over
`Char` and lives in `Meyer.Book.Examples`. -/

section Nondeterminism

variable [Lettered α]

/-- With one letter `c`, the input `c cc c`. -/
def tIn (c : α) : Text α := [c, blank, c, c, blank, c]

/-- `c cc / c`. -/
def tOut₁ (c : α) : Text α := [c, blank, c, c, newline, c]

/-- `c / cc c`. -/
private def tOut₂ (c : α) : Text α := [c, newline, c, c, blank, c]

private lemma words_tIn [DecidableEq α] {c : α} (hc : ¬ IsBreak c) :
    words (tIn c) = [[c], [c, c], [c]] := by
  have hl : ∀ x ∈ [c, c], IsLetter x := by
    intro x hx
    rw [List.mem_cons, List.mem_singleton, or_self] at hx
    exact hx ▸ hc
  rw [tIn, show [c, blank, c, c, blank, c] = [c] ++ blank :: ([c, c] ++ blank :: [c]) from rfl,
    words_append_sep (Or.inl rfl), words_append_sep (Or.inl rfl),
    words_of_forall_letter (List.cons_ne_nil _ _) fun x hx => hl x (List.mem_cons_of_mem _ hx),
    words_of_forall_letter (List.cons_ne_nil _ _) hl]
  rfl

/-- Six characters is the least a recast of `c cc c` can have: four letters and
two gaps. -/
private lemma six_le_length_of_recast [DecidableEq α] {c : α} (hc : ¬ IsBreak c) {y : Text α}
    (h : Recast (tIn c) y) : 6 ≤ y.length := by
  have hb := le_length_of_recast h
  rw [words_tIn hc] at hb
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_cons,
    List.length_nil] at hb
  omega

/-- Six characters is the minimum, so any six-character recast attains it. -/
lemma mem_minRecasts_of_length_six [DecidableEq α] {c : α} (hc : ¬ IsBreak c)
    {o : Text α} (ho : Recast (tIn c) o) (h : o.length = 6) : o ∈ MinRecasts (tIn c) :=
  mem_minRecasts_iff.2 ⟨ho, fun _ hy => h ▸ six_le_length_of_recast hc hy⟩

/-- Nothing acceptable fits on one line: a shortest recast has six characters
and `M` is four. -/
lemma one_le_newLines_tIn [DecidableEq α] {c : α} (hc : ¬ IsBreak c) {y : Text α}
    (hy : y ∈ MinRecasts (tIn c)) (hmax : maxLine y ≤ 4) : 1 ≤ newLines y := by
  refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
  have hnn : newline ∉ y := List.count_eq_zero.1 h0
  have h6 := six_le_length_of_recast hc (mem_minRecasts_iff.1 hy).1
  have := length_le_maxLine_of_no_newline hnn
  omega

/-- `c cc c` recasts to `c cc / c` by `[R]` on its second break. -/
lemma recast_tOut₁ (c : α) : Recast (tIn c) (tOut₁ c) :=
  recast_of_recast1 (by
    simpa [tIn, tOut₁] using recast1_replace (b := [blank]) (x := [c, blank, c, c]) (y := [c])
      (singleton_mem_break (Or.inl rfl)) (s := newline) (Or.inr rfl))

private lemma recast_tOut₂ (c : α) : Recast (tIn c) (tOut₂ c) :=
  recast_of_recast1 (by
    simpa [tIn, tOut₂] using recast1_replace (b := [blank]) (x := [c]) (y := [c, c, blank, c])
      (singleton_mem_break (Or.inl rfl)) (s := newline) (Or.inr rfl))

/-- A new line splits the runs, and neither side is longer than four. -/
lemma maxLine_le_four {x y : Text α} (hx : x.length ≤ 4) (hy : y.length ≤ 4) :
    maxLine (x ++ [newline] ++ y) ≤ 4 := by
  rw [maxLine, maxRun_append_mid (by simp) (by simp)]
  exact max_le (maxRun_le fun t ht _ => ht.length_le.trans hx)
    (maxRun_le fun t ht _ => ht.length_le.trans hy)

/-- `c cc / c` is a solution.  `Meyer.Book.Bug` reuses this. -/
lemma goal_tOut₁ [DecidableEq α] {c : α} (hc : ¬ IsBreak c)
    (h : (blank : α) ≠ newline) : Goal 4 (tIn c) (tOut₁ c) := by
  have hcn : c ≠ newline := fun e => hc (Or.inr e)
  refine mem_solutions_iff.2 ⟨⟨mem_minRecasts_of_length_six hc (recast_tOut₁ c) rfl,
    maxLine_le_four (x := [c, blank, c, c]) (y := [c]) (by simp) (by simp)⟩, fun y hy hmy => ?_⟩
  rw [show newLines (tOut₁ c) = 1 from by simp [newLines, tOut₁, hcn, h]]
  exact one_le_newLines_tIn hc hy hmy

private lemma goal_tOut₂ [DecidableEq α] {c : α} (hc : ¬ IsBreak c)
    (h : (blank : α) ≠ newline) : Goal 4 (tIn c) (tOut₂ c) := by
  have hcn : c ≠ newline := fun e => hc (Or.inr e)
  refine mem_solutions_iff.2 ⟨⟨mem_minRecasts_of_length_six hc (recast_tOut₂ c) rfl,
    maxLine_le_four (x := [c]) (y := [c, c, blank, c]) (by simp) (by simp)⟩, fun y hy hmy => ?_⟩
  rw [show newLines (tOut₂ c) = 1 from by simp [newLines, tOut₂, hcn, h]]
  exact one_le_newLines_tIn hc hy hmy

/-- **`T5`**: "Can there be more than one solution for a given input?  ... the
answer in the formal specification is a clear yes."  On any alphabet with a
letter and two distinct separators. -/
theorem goal_not_functional [DecidableEq α] (h : (blank : α) ≠ newline) :
    ∃ (M : ℕ) (i o₁ o₂ : Text α), Goal M i o₁ ∧ Goal M i o₂ ∧ o₁ ≠ o₂ := by
  obtain ⟨c, hc⟩ := Lettered.exists_letter (α := α)
  exact ⟨4, tIn c, tOut₁ c, tOut₂ c, goal_tOut₁ hc h, goal_tOut₂ hc h,
    by simp [tOut₁, tOut₂, h]⟩

end Nondeterminism

/-! ## Where the two separators coincide

`T5`'s hypothesis that `space` and `new_line` are two characters is needed for
more than the witness: where they are one, `S1` is a partial function.  A
shortest recast has no separator at either end (`T6`) and no two side by side,
since `[R]` would shorten it; with a single separator character it is therefore
its words joined by that character, and by `T3` its words are those of the
input.  Put the other way, with one separator every way of breaking the words
into lines prints the same text.  That is proved here directly and not through
`Native.byLayout_eq_book`, which is stated at `Char`, where the two separators
differ.  The 1985 counterpart is `Meyer.Paper.eq_of_goal_of_blank_eq_newline`. -/

section Coincide

variable [DecidableEq α] [Alphabet α]

omit [DecidableEq α] in
/-- A shortest recast has no two separators side by side: `[R]` would replace
them by one. -/
private lemma not_isSeparator_of_adjacent {i o : Text α} (ho : o ∈ MinRecasts i)
    {x y : Text α} {a b : α} (h : o = x ++ a :: b :: y) (ha : IsSeparator a) :
    ¬ IsSeparator b := by
  intro hb
  obtain ⟨hor, homin⟩ := mem_minRecasts_iff.1 ho
  have hab : [a, b] ∈ Break := ⟨List.cons_ne_nil _ _, fun c hc => by
    rcases List.mem_pair.1 hc with rfl | rfl <;> assumption⟩
  have hstep : Recast1 o (x ++ [a] ++ y) := by
    rw [h, show x ++ a :: b :: y = x ++ [a, b] ++ y by simp]
    exact recast1_replace hab ha
  have := homin _ (recast_trans hor (recast_of_recast1 hstep))
  rw [h] at this
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- A text splits at its first separator, if it has one. -/
private lemma exists_eq_append_first {t : Text α} (h : ∃ c ∈ t, IsSeparator c) :
    ∃ w c r, t = w ++ c :: r ∧ (∀ x ∈ w, IsLetter x) ∧ IsSeparator c := by
  induction t with
  | nil => simp at h
  | cons d t ih =>
    by_cases hd : IsSeparator d
    · exact ⟨[], d, t, rfl, by simp, hd⟩
    · obtain ⟨w, c, r, rfl, hw, hc⟩ := ih (by simpa [hd] using h)
      exact ⟨d :: w, c, r, rfl, by simpa [IsLetter] using ⟨hd, hw⟩, hc⟩

/-- A text with no separator at either end and none side by side, over an
alphabet whose one separator is `space`, is its words joined by spaces. -/
private lemma eq_intercalate_words (hsep : ∀ c : α, IsSeparator c → c = blank)
    (t : Text α)
    (h₁ : ∀ c r, t = c :: r → ¬ IsSeparator c)
    (h₂ : ∀ r c, t = r ++ [c] → ¬ IsSeparator c)
    (h₃ : ∀ x y a b, t = x ++ a :: b :: y → IsSeparator a → ¬ IsSeparator b) :
    t = List.intercalate [blank] (words t) := by
  by_cases hall : ∃ c ∈ t, IsSeparator c
  · obtain ⟨w, c, r, rfl, hw, hc⟩ := exists_eq_append_first hall
    have hwne : w ≠ [] := by rintro rfl; exact h₁ c r rfl hc
    have hrne : r ≠ [] := by rintro rfl; exact h₂ w c rfl hc
    have ih := eq_intercalate_words hsep r
      (fun d r' hr => h₃ w r' c d (by rw [hr]) hc)
      (fun r' d hr => h₂ (w ++ c :: r') d (by simp [hr]))
      (fun x y a b hr => h₃ (w ++ c :: x) y a b (by simp [hr]))
    obtain ⟨v, vs, hv⟩ := List.exists_cons_of_ne_nil (l := words r)
      fun h0 => hrne (ih.trans (by rw [h0]; rfl))
    rw [words_append_sep hc, words_of_forall_letter hwne hw, hv, List.singleton_append,
      List.intercalate_cons_cons, ← hv, ← ih, hsep c hc]
    simp
  · simp only [not_exists, not_and] at hall
    rcases eq_or_ne t [] with rfl | hne
    · rfl
    · rw [words_of_forall_letter hne hall]
      simp
termination_by t.length
decreasing_by subst_vars; simp only [List.length_append, List.length_cons]; omega

/-- Where the two separators coincide, a shortest recast is the input's words
joined by spaces. -/
lemma eq_of_mem_minRecasts (hbn : (blank : α) = newline) {i o : Text α}
    (ho : o ∈ MinRecasts i) : o = List.intercalate [blank] (words i) := by
  rw [← words_eq_of_recast (mem_minRecasts_iff.1 ho).1]
  exact eq_intercalate_words (fun c hc => hc.elim id (·.trans hbn.symm)) o
    (fun _ _ h => head_not_isSeparator ho h) (fun _ _ h => getLast_not_isSeparator ho h)
    (fun _ _ _ _ h ha => not_isSeparator_of_adjacent ho h ha)

/-- Where the two separators coincide, `S1` has at most one output. -/
theorem eq_of_goal_of_blank_eq_newline (hbn : (blank : α) = newline) {M : ℕ}
    {i o₁ o₂ : Text α} (h₁ : Goal M i o₁) (h₂ : Goal M i o₂) : o₁ = o₂ :=
  (eq_of_mem_minRecasts hbn (solutions_subset_minRecasts M i h₁)).trans
    (eq_of_mem_minRecasts hbn (solutions_subset_minRecasts M i h₂)).symm

/-- **`T5` needs two separators.**  "Can there be more than one solution for a
given input?  ... a clear yes" fails on every alphabet where `space` and
`new_line` coincide. -/
theorem blank_ne_newline_of_not_functional
    (h : ∃ (M : ℕ) (i o₁ o₂ : Text α), Goal M i o₁ ∧ Goal M i o₂ ∧ o₁ ≠ o₂) :
    (blank : α) ≠ newline := by
  obtain ⟨_, _, _, _, h₁, h₂, hne⟩ := h
  exact fun hbn => hne (eq_of_goal_of_blank_eq_newline hbn h₁ h₂)

end Coincide


end Meyer.Book
