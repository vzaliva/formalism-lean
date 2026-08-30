import Native.Properties
import Meyer.Book.Facts

/-!
# The Lean-native specification against the book's

`Native.ByLayout` is the same relation as the book's `S1`, `byLayout_iff_book`.  So
everything the chapter proves about `S1` holds of `ByLayout` as well -- `T1` is
transferred explicitly as `length_le_of_byLayout`, the inequality
`Native.length_of_byLayout` sharpens -- and, since `Meyer.Comparison` proves the
book's relation different from the paper's, `ByLayout` differs from the 1985
relation too.  That corollary is not restated here.

The equivalence runs through one observation: a shortest recast of `i` is the
printed form of a cut of the words of `i`, and every such printed form is a
shortest recast.  The forward half rests on the book's `[L]`, `[T]` and `[R]`
each shortening a text that has a separator at an end or two side by side, so
that a shortest recast is a text of the kind `Native.exists_cut_of_tight` parses;
`T3` then identifies its words with those of `i`.  The backward half reaches any
printed cut from some shortest recast by exchanging separators one at a time and
attains the length bound of exercise 9-E.6, `Meyer.Book.le_length_of_recast`.
On a printed cut, `maxline ≤ M` says every line fits and `new_lines` counts the
lines less one, so the book's two minimisations are the layout's one.
-/

namespace Native

open Meyer

/-- `words` is the book's `WORDS`, which the docstring of `Native.words` already
says; this is what lets the book's `T3` and its length bound be used here. -/
private lemma words_eq_book (t : Text) : words t = Book.words t :=
  List.filter_congr fun w _ => by cases w <;> simp

/-! ## Shortest recasts are printed cuts -/

/-- A shortest recast has no two adjacent separators: `[R]` would shorten it.
In the paper's vocabulary, it satisfies `NoDoubleBreak`. -/
private lemma not_adjacent_of_mem_minRecasts {i o : Text} (ho : o ∈ Book.MinRecasts i) :
    ∀ x s s' y, o = x ++ s :: s' :: y → IsBreak s → ¬ IsBreak s' := by
  obtain ⟨hor, homin⟩ := Book.mem_minRecasts_iff.1 ho
  intro x s s' y h hs hs'
  have hstep : Book.Recast1 o (x ++ [s] ++ y) := by
    rw [h, show x ++ s :: s' :: y = x ++ [s, s'] ++ y by simp]
    exact Book.recast1_replace ⟨by simp, by simp [hs, hs']⟩ hs
  have := homin _ (Book.recast_trans hor (Book.recast_of_recast1 hstep))
  rw [h] at this
  simp at this
  omega

/-- **A shortest recast of `i` is a printed cut of the words of `i`.**  The cut is
of the words of the recast, which are the words of `i` by `T3`. -/
private lemma exists_cut_of_mem_minRecasts {i o : Text} (ho : o ∈ Book.MinRecasts i) :
    ∃ ls : List Line, [] ∉ ls ∧ ls.flatten = words i ∧ o = render ls := by
  obtain ⟨ls, hne, hw, rfl⟩ := exists_cut_of_tight (not_adjacent_of_mem_minRecasts ho)
    (fun _ _ h => Book.head_not_isSeparator ho h) (fun _ _ h => Book.getLast_not_isSeparator ho h)
  refine ⟨ls, hne, ?_, rfl⟩
  rw [← words_render hw, words_eq_book, words_eq_book,
    Book.words_eq_of_recast (Book.mem_minRecasts_iff.1 ho).1]

/-- Exchanging separators one at a time is a recast: each exchange is `[R]` on a
break of one character.  This is the construction behind the book's `owpl`,
`Meyer.Book.recast_allNewlines`, with the target left free. -/
private lemma recast_of_forall₂ {x y : Text}
    (h : List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) x y) :
    Book.Recast x y := by
  refine Relation.ReflTransGen.mono (fun _ _ h => Book.recast1_of_recast1R h) ?_
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b x y hab _ ih =>
    refine (Book.recastR_cons ih).trans ?_
    rcases hab with rfl | ⟨ha, hb⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ⟨[a], Book.singleton_mem_break ha, b, hb, [], y, by simp, by simp⟩

/-- **Every printed cut of the words of `i` is a shortest recast of `i`.**  It is
reached from some shortest recast, itself a printed cut, by exchanging
separators; and it attains the length bound every recast satisfies. -/
private lemma render_mem_minRecasts {i : Text} {ls : List Line} (hne : [] ∉ ls)
    (hf : ls.flatten = words i) : render ls ∈ Book.MinRecasts i := by
  obtain ⟨o₀, ho₀⟩ := Book.minRecasts_nonempty i
  obtain ⟨ls₀, hne₀, hf₀, rfl⟩ := exists_cut_of_mem_minRecasts ho₀
  obtain ⟨hor, -⟩ := Book.mem_minRecasts_iff.1 ho₀
  refine Book.mem_minRecasts_iff.2
    ⟨Book.recast_trans hor (recast_of_forall₂ (forall₂_render_cut hne₀ hf₀ hne hf)),
      fun y hy => ?_⟩
  have hb := Book.le_length_of_recast hy
  rw [← words_eq_book] at hb
  by_cases hw : words i = []
  · rw [eq_nil_of_cut hne (hw ▸ hf), render_nil]; simp
  · have := length_render_cut hw hne hf
    omega

/-! ## Lines and new lines of a printed cut -/

/-- `new_lines` of a printed cut is one less than its number of lines:
`Native.count_newline_render`, in the book's terms. -/
private lemma newLines_render {ls : List Line} (hne : ls ≠ [])
    (h : ∀ l ∈ ls, newline ∉ renderLine l) : Book.newLines (render ls) + 1 = ls.length :=
  count_newline_render hne h

/-- A text without a new line is a single line of its own length. -/
private lemma maxLine_eq_length {t : Text} (h : newline ∉ t) : Book.maxLine t = t.length :=
  le_antisymm (maxRun_le fun _ ht _ => ht.length_le)
    (le_maxRun (List.infix_refl t) fun _ hc hcn => h (hcn ▸ hc))

/-- `maxline` of a printed cut is bounded by `M` exactly when every line is.  The
new lines split the runs, `Meyer.Common.maxRun_append_mid`. -/
private lemma maxLine_render_le_iff {M : ℕ} : ∀ {ls : List Line},
    (∀ l ∈ ls, newline ∉ renderLine l) →
    (Book.maxLine (render ls) ≤ M ↔ ∀ l ∈ ls, (renderLine l).length ≤ M)
  | [], _ => by simp [Book.maxLine]
  | [l], h => by rw [render_singleton, maxLine_eq_length (h l (by simp))]; simp
  | l :: l' :: ls, h => by
    have ih := maxLine_render_le_iff (M := M) fun l'' hl'' => h l'' (List.mem_cons_of_mem _ hl'')
    rw [render_cons_cons, show renderLine l ++ newline :: render (l' :: ls) =
      renderLine l ++ [newline] ++ render (l' :: ls) by simp, Book.maxLine,
      maxRun_append_mid (by simp) (by simp), max_le_iff, ← Book.maxLine, ← Book.maxLine, ih,
      maxLine_eq_length (h l (by simp))]
    simp

/-! ## The equivalence -/

/-- **The book's specification is this one.**  `ByLayout M i o ↔ Meyer.Book.Goal M i o`.

Reading the book's `S1` through the lemmas above: its shortest recasts are the
printed cuts of the words of the input; `maxline ≤ M` on a printed cut says that
every line fits; and `new_lines` counts the lines less one.  So minimising
`new_lines` over the shortest recasts with `maxline ≤ M` is minimising the
number of lines over the layouts, and `S1` and `ByLayout` accept the same
outputs. -/
theorem byLayout_iff_book (M : ℕ) (i o : Text) : ByLayout M i o ↔ Book.Goal M i o := by
  have hnl : ∀ ls : List Line, ls.flatten = words i → ∀ l ∈ ls, newline ∉ renderLine l :=
    fun ls hf l hl => newline_not_mem_renderLine fun w hw => (words_of_cut hf l hl w hw).2
  rw [Book.Goal, Book.mem_solutions_iff]
  constructor
  · rintro ⟨ls, hl, hmin, rfl⟩
    refine ⟨⟨render_mem_minRecasts hl.nonempty hl.flatten,
      (maxLine_render_le_iff (hnl ls hl.flatten)).2 hl.fits⟩, fun y hy hmy => ?_⟩
    obtain ⟨ls', hne', hf', rfl⟩ := exists_cut_of_mem_minRecasts hy
    have hlen := hmin ls' ⟨hf', hne', (maxLine_render_le_iff (hnl ls' hf')).1 hmy⟩
    rcases ls with _ | ⟨l, ls⟩
    · simp [Book.newLines, render_nil]
    · have h₁ := newLines_render (List.cons_ne_nil l ls) (hnl _ hl.flatten)
      have h₂ := newLines_render (by rintro rfl; simp at hlen) (hnl _ hf')
      omega
  · rintro ⟨⟨hmem, hmax⟩, hmin⟩
    obtain ⟨ls, hne, hf, rfl⟩ := exists_cut_of_mem_minRecasts hmem
    refine ⟨ls, ⟨hf, hne, (maxLine_render_le_iff (hnl ls hf)).1 hmax⟩,
      fun ls' hl' => ?_, rfl⟩
    have hlen := hmin (render ls') (render_mem_minRecasts hl'.nonempty hl'.flatten)
      ((maxLine_render_le_iff (hnl ls' hl'.flatten)).2 hl'.fits)
    rcases ls' with _ | ⟨l', ls'⟩
    · have hw : words i = [] := by simpa using hl'.flatten.symm
      rw [eq_nil_of_cut hne (hw ▸ hf)]
    · rcases ls with _ | ⟨l, ls⟩
      · simp
      · have h₁ := newLines_render (List.cons_ne_nil l ls) (hnl _ hf)
        have h₂ := newLines_render (List.cons_ne_nil l' ls') (hnl _ hl'.flatten)
        omega

/-- The book's `T1` for `ByLayout`, the inequality `Native.length_of_byLayout` sharpens: an output
is no
longer than its input.  Through `byLayout_iff_book`, an output is a recast of the
input, and `Meyer.Book.length_le_of_recast` is `T1`. -/
theorem length_le_of_byLayout {M : ℕ} {i o : Text} (h : ByLayout M i o) : o.length ≤ i.length :=
  Book.length_le_of_recast
    (Book.mem_minRecasts_iff.1
      (Book.solutions_subset_minRecasts M i ((byLayout_iff_book M i o).1 h))).1

end Native
