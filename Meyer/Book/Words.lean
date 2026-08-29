import Meyer.Book.Recast

/-!
# Words and breaks

Exercise 9-E.6: "Give formal definitions of `WORDS (t)` and `breaks (t)`,
respectively the sequences of words and breaks of a text `t`, used in `T3` and
`T4`.  (*Hint*: prove that `t` can be written in exactly one way in the form
`b₀ + Σᵢ (wᵢ + bᵢ)` for words `wᵢ`, all non-empty, and breaks `bᵢ`, all non-empty
except possibly `b₀` or `bₙ` or both.)"

Both are `runsOf`, the non-empty maximal stretches on which a predicate fails,
taken here at "is a separator" and at "is a letter".  Splitting a list at the
positions where a predicate holds is `List.splitOnP`.

Only the first half of the exercise is done here.  `WORDS` and `breaks` are
defined, and the properties `T3` and `T4` need are proved; the existence and
uniqueness of the alternating decomposition `b₀ + Σᵢ (wᵢ + bᵢ)` is not stated as
a theorem.  Nothing below rests on it.

The module supplies three things to `Meyer.Book.Facts`:

* `T3`, `words_eq_of_recast`: recasting does not change the words.
* `T4`, `length_breaks_ge`.
* `length_add_length_words_le`, the bound that makes a recast's length at least
  the length of its one-word-per-line form.  This is the step Meyer's proof of
  the feasibility theorem `T8` passes over -- see the module docstring of
  `Meyer.Book.Facts`.
-/

namespace Meyer.Book

open List

/-! ## Runs

`runsOf p t` is the list of non-empty maximal stretches of `t` containing no
character satisfying `p`.  `words` is `runsOf` at "is a separator" and `breaks`
is `runsOf` at "is a letter". -/

/-- The non-empty maximal stretches of `t` on which `p` fails. -/
private noncomputable def runsOf (p : Char → Bool) (t : Text) : List Text :=
  (t.splitOnP p).filter fun w => !w.isEmpty

private lemma words_eq_runsOf (t : Text) : words t = runsOf (fun c => decide (IsSeparator c)) t :=
  rfl

private lemma breaks_eq_runsOf (t : Text) : breaks t = runsOf (fun c => decide (IsLetter c)) t :=
  rfl

/-- The two predicates are complementary, which is what couples `words` to
`breaks`. -/
private lemma letterP_eq (c : Char) :
    decide (IsLetter c) = !decide (IsSeparator c) := by
  simp [IsLetter]

@[simp] private lemma runsOf_nil (p : Char → Bool) : runsOf p [] = [] := by
  simp [runsOf, List.splitOnP_nil]

/-- At a character where `p` holds, a run ends: the list of runs is unchanged. -/
private lemma runsOf_cons_pos {p : Char → Bool} {c : Char} (hc : p c = true) (t : Text) :
    runsOf p (c :: t) = runsOf p t := by
  simp [runsOf, List.splitOnP_cons_eq_if_modifyHead, hc]

/-- At a character where `p` fails, the character joins the first run, creating
it if the first run was empty. -/
private lemma runsOf_cons_neg {p : Char → Bool} {c : Char} (hc : p c = false) (t : Text) :
    runsOf p (c :: t) = (c :: (t.splitOnP p).headD []) :: (t.splitOnP p).tail.filter
      (fun w => !w.isEmpty) := by
  obtain ⟨h, l, hl⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p t)
  simp [runsOf, List.splitOnP_cons_eq_if_modifyHead, hc, hl]

private lemma runsOf_eq_tail_filter {p : Char → Bool} {t : Text}
    (h : (t.splitOnP p).headD [] = []) :
    runsOf p t = (t.splitOnP p).tail.filter (fun w => !w.isEmpty) := by
  obtain ⟨hd, l, hl⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p t)
  rw [hl] at h ⊢
  simp_all [runsOf]

private lemma runsOf_eq_cons_tail_filter {p : Char → Bool} {t : Text}
    (h : (t.splitOnP p).headD [] ≠ []) :
    runsOf p t = (t.splitOnP p).headD [] :: (t.splitOnP p).tail.filter
      (fun w => !w.isEmpty) := by
  obtain ⟨hd, l, hl⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p t)
  rw [hl] at h ⊢
  simp_all [runsOf]

/-- A run is never empty. -/
private lemma ne_nil_of_mem_runsOf {p : Char → Bool} {t w : Text} (h : w ∈ runsOf p t) :
    w ≠ [] := by
  have := List.of_mem_filter h
  simpa using this

/-! ## Flattening

The runs of `t` hold exactly the characters of `t` at which `p` fails, in
order. -/

private lemma flatten_runsOf (p : Char → Bool) (t : Text) :
    (runsOf p t).flatten = t.filter (fun c => !p c) := by
  induction t with
  | nil => simp
  | cons c t ih =>
    by_cases hc : p c
    · rw [runsOf_cons_pos hc, ih, List.filter_cons_of_neg (by simp [hc])]
    · rw [List.filter_cons_of_pos (by simp [Bool.eq_false_iff.1 (by simpa using hc)]),
        runsOf_cons_neg (by simpa using hc), List.flatten_cons, List.cons_append]
      congr 1
      by_cases h : (t.splitOnP p).headD [] = []
      · rw [runsOf_eq_tail_filter h] at ih; rw [h]; simpa using ih
      · rw [runsOf_eq_cons_tail_filter h] at ih; simpa using ih

/-- Each run has at least one character. -/
private lemma length_le_length_flatten (p : Char → Bool) (t : Text) :
    (runsOf p t).length ≤ (runsOf p t).flatten.length := by
  have : ∀ l : List Text, ([] ∉ l) → l.length ≤ l.flatten.length := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
      intro h
      have hw : w ≠ [] := fun hcon => h (hcon ▸ List.mem_cons_self ..)
      have := ih fun hcon => h (List.mem_cons_of_mem _ hcon)
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      have : 1 ≤ w.length := Nat.one_le_iff_ne_zero.2 fun hcon =>
        hw (List.eq_nil_of_length_eq_zero hcon)
      omega
  exact this _ fun hcon => ne_nil_of_mem_runsOf hcon rfl

/-- The characters of a text are its letters and its separators. -/
private lemma length_flatten_words_add_length_flatten_breaks (t : Text) :
    (words t).flatten.length + (breaks t).flatten.length = t.length := by
  rw [words_eq_runsOf, breaks_eq_runsOf, flatten_runsOf, flatten_runsOf]
  simp only [letterP_eq, Bool.not_not]
  rw [Nat.add_comm]
  exact (List.length_eq_length_filter_add (l := t) (fun c => decide (IsSeparator c))).symm

/-! ## Counting runs

A text's letter-runs and separator-runs alternate, so their numbers differ by at
most one.  The bookkeeping goes through the head of the split, which is empty
exactly when the text is empty or starts with a character satisfying `p`. -/

private lemma headD_splitOnP_nil (p : Char → Bool) :
    ((([] : Text)).splitOnP p).headD [] = [] := by
  simp [List.splitOnP_nil]

private lemma headD_splitOnP_cons (p : Char → Bool) (c : Char) (t : Text) :
    (((c :: t)).splitOnP p).headD [] = [] ↔ p c = true := by
  by_cases hc : p c
  · simp [List.splitOnP_cons_eq_if_modifyHead, hc]
  · obtain ⟨hd, l, hl⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p t)
    simp [List.splitOnP_cons_eq_if_modifyHead, hc, hl]

private lemma length_runsOf_cons_pos {p : Char → Bool} {c : Char} (hc : p c = true) (t : Text) :
    (runsOf p (c :: t)).length = (runsOf p t).length := by
  rw [runsOf_cons_pos hc]

private lemma length_runsOf_cons_neg {p : Char → Bool} {c : Char} (hc : p c = false) (t : Text) :
    (runsOf p (c :: t)).length =
      (runsOf p t).length + (if (t.splitOnP p).headD [] = [] then 1 else 0) := by
  rw [runsOf_cons_neg hc]
  by_cases h : (t.splitOnP p).headD [] = []
  · rw [if_pos h, runsOf_eq_tail_filter h]; simp
  · rw [if_neg h, runsOf_eq_cons_tail_filter h]; simp

/-- **The alternation bound.**  Letter-runs and separator-runs interleave, so
neither can outnumber the other by more than one. -/
private lemma length_runsOf_le (p : Char → Bool) (t : Text) :
    (runsOf p t).length ≤ (runsOf (fun c => !p c) t).length +
      (if (t.splitOnP p).headD [] = [] then 0 else 1) := by
  induction t with
  | nil => simp
  | cons c t ih =>
    by_cases hc : p c
    · have hq : (fun c => !p c) c = false := by simp [hc]
      rw [length_runsOf_cons_pos hc, length_runsOf_cons_neg hq,
        if_pos ((headD_splitOnP_cons p c t).2 hc)]
      have hmono : (if (t.splitOnP p).headD [] = [] then 0 else 1) ≤
          (if (t.splitOnP (fun c => !p c)).headD [] = [] then 1 else 0) := by
        by_cases h : (t.splitOnP p).headD [] = []
        · rw [if_pos h]; exact Nat.zero_le _
        · rw [if_neg h]
          rcases t with _ | ⟨d, t'⟩
          · exact absurd (headD_splitOnP_nil p) h
          · have hd : p d = false := by
              by_contra hcon
              exact h ((headD_splitOnP_cons p d t').2 (by simpa using hcon))
            rw [if_pos ((headD_splitOnP_cons (fun c => !p c) d t').2 (by simp [hd]))]
      omega
    · have hcf : p c = false := by simpa using hc
      have hq : (fun c => !p c) c = true := by simp [hcf]
      rw [if_neg (show ¬ ((c :: t).splitOnP p).headD [] = [] by
            rw [headD_splitOnP_cons]; simp [hcf]),
        length_runsOf_cons_neg hcf, length_runsOf_cons_pos hq]
      by_cases h : (t.splitOnP p).headD [] = []
      · rw [if_pos h]; rw [if_pos h] at ih; omega
      · rw [if_neg h]; rw [if_neg h] at ih; omega

/-! ## `words` and `breaks` -/

@[simp] private lemma words_nil : words ([] : Text) = [] := by simp [words_eq_runsOf]

@[simp] private lemma breaks_nil : breaks ([] : Text) = [] := by simp [breaks_eq_runsOf]

/-- A separator ends a word. -/
private lemma words_cons_sep {c : Char} (hc : IsSeparator c) (t : Text) :
    words (c :: t) = words t := by
  rw [words_eq_runsOf, words_eq_runsOf, runsOf_cons_pos (by simpa using hc)]

/-- The words of a text made only of separators: there are none. -/
lemma words_of_forall_sep {b : Text} (h : ∀ c ∈ b, IsSeparator c) : words b = [] := by
  induction b with
  | nil => simp
  | cons c t ih =>
    rw [words_cons_sep (h c (List.mem_cons_self ..))]
    exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- A text with no separator in it is one word. -/
lemma words_of_forall_letter {w : Text} (hne : w ≠ []) (h : ∀ c ∈ w, IsLetter c) :
    words w = [w] := by
  rw [words_eq_runsOf, runsOf, List.splitOnP_eq_singleton (fun c hc => by simpa using h c hc)]
  simp [hne]

/-- **Words split at a separator.**  Everything about `words` follows from this
one equation. -/
lemma words_append_sep {c : Char} (hc : IsSeparator c) (x y : Text) :
    words (x ++ c :: y) = words x ++ words y := by
  rw [words_eq_runsOf, words_eq_runsOf, words_eq_runsOf, runsOf,
    List.splitOnP_append_cons x y (by simpa using hc), List.filter_append]
  rfl

/-- The same for a whole break. -/
private lemma words_append_break {b : Text} (hb : b ∈ Break) :
    ∀ x y : Text, words (x ++ b ++ y) = words x ++ words y := by
  obtain ⟨hne, hsep⟩ := hb
  induction b with
  | nil => exact absurd rfl hne
  | cons c b ih =>
    intro x y
    rw [show x ++ (c :: b) ++ y = x ++ c :: (b ++ y) by simp,
      words_append_sep (hsep c (List.mem_cons_self ..))]
    rcases b with _ | ⟨d, b'⟩
    · simp
    · rw [show d :: b' ++ y = [] ++ (d :: b') ++ y by simp,
        ih (by simp) (fun a ha => hsep a (List.mem_cons_of_mem _ ha)) [] y]
      simp

/-! ## `T3` -/

private lemma words_eq_of_recast1 {i o : Text} (h : Recast1 i o) : words i = words o := by
  obtain ⟨b, hb, h⟩ := h
  rcases h with rfl | rfl | ⟨s, hs, x, y, rfl, rfl⟩
  · rw [show b ++ o = [] ++ b ++ o by simp, words_append_break hb]; simp
  · rw [show o ++ b = o ++ b ++ [] by simp, words_append_break hb]; simp
  · rw [words_append_break hb, words_append_break (singleton_mem_break hs)]

/-- **`T3`**: `WORDS (out) = WORDS (in)`.

Meyer: "we note that the three transformations `[L]`, `[R]` and `[S]` in the
definition of `recast1` affect separators only and hence have no influence on the
words of `in`."  The remark is correct; the reflexive transitive closure supplies
the induction it needs. -/
theorem words_eq_of_recast {i o : Text} (h : Recast i o) : words o = words i := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (words_eq_of_recast1 hstep).symm.trans ih

/-! ## `T4` -/

/-- Letter-runs never outnumber separator-runs by more than one, and vice
versa. -/
private lemma length_words_le (t : Text) : (words t).length ≤ (breaks t).length + 1 := by
  have h := length_runsOf_le (fun c => decide (IsSeparator c)) t
  rw [← words_eq_runsOf] at h
  have hb : runsOf (fun c => !decide (IsSeparator c)) t = breaks t := by
    rw [breaks_eq_runsOf]; congr 1; funext c; rw [letterP_eq]
  rw [hb] at h
  split at h <;> omega

private lemma length_breaks_le (t : Text) : (breaks t).length ≤ (words t).length + 1 := by
  have h := length_runsOf_le (fun c => decide (IsLetter c)) t
  rw [← breaks_eq_runsOf] at h
  have hw : runsOf (fun c => !decide (IsLetter c)) t = words t := by
    rw [words_eq_runsOf]; congr 1; funext c; rw [letterP_eq]; simp
  rw [hw] at h
  split at h <;> omega

/-- **`T4`**: `breaks (out).count ≥ breaks (in).count - 2`.

Meyer: "these transformations only affect the number of breaks except by possibly
removing a heading break, a trailing break or both."  With `T3` in hand it is a
consequence of the alternation of words and breaks. -/
theorem length_breaks_ge {i o : Text} (h : Recast i o) :
    (breaks i).length ≤ (breaks o).length + 2 := by
  have h1 := length_breaks_le i
  have h2 := length_words_le o
  rw [words_eq_of_recast h] at h2
  omega

/-! ## The length of a recast

The bound `T8` needs and Meyer's proof of it does not mention: a text is at least
as long as its letters plus one separator between each pair of consecutive
words. -/

/-- Every text is at least as long as its one-word-per-line form. -/
lemma length_add_length_words_le (t : Text) :
    (words t).flatten.length + (words t).length ≤ t.length + 1 := by
  have h1 := length_flatten_words_add_length_flatten_breaks t
  have h2 : (breaks t).length ≤ (breaks t).flatten.length := by
    rw [breaks_eq_runsOf]; exact length_le_length_flatten _ t
  have h3 := length_words_le t
  omega

/-- Consequently every recast of `i` has at least that length. -/
lemma le_length_of_recast {i o : Text} (h : Recast i o) :
    (words i).flatten.length + (words i).length ≤ o.length + 1 := by
  rw [← words_eq_of_recast h]
  exact length_add_length_words_le o

end Meyer.Book
