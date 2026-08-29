import Native.Spec
import Meyer.Comparison

/-!
# Properties of the Lean-native specification

What can be said about `Native.Goal`, and how it stands to Meyer's two
specifications.

* **Decidability.**  A layout of a finite list of words is one of finitely many
  cuts of that list, so `Layout` and `Goal` are decidable and concrete claims are
  settled by `decide`.  The specification stays a proposition; that it can be
  evaluated is a theorem about it, not part of it.
* **Feasibility**, the counterpart of the book's `T8` and the paper's domain
  theorem: an input has an output exactly when each of its words fits on a line.
* **Nondeterminism**, the counterpart of the book's `T5` and the paper's second
  claim, on Meyer's own example.
* **The book's relation is this one.**  `goal_iff_book` proves `Goal M i o ↔
  Meyer.Book.Goal M i o`, so everything the chapter proves about `S1` holds of
  `Goal` as well, and `Meyer.Comparison.specifications_differ` places `Goal`
  apart from the 1985 relation.

The proof of the equivalence runs through one observation: a shortest recast of
`i` is the printed form of a cut of the words of `i`, and every such printed
form is a shortest recast.  Both directions are proved here from the book's own
lemmas, `T3` in particular; nothing about the recasting relation is developed
afresh.
-/

namespace Native

open Meyer List

noncomputable section

/-! ## Words -/

/-- `words` is the book's `WORDS`, which the module docstring of `Native.Spec`
already says; this makes the book's lemmas about it available. -/
lemma words_eq_book (t : Text) : words t = Book.words t :=
  List.filter_congr fun w _ => by cases w <;> simp

/-- No piece of a split contains a character that was split on. -/
private lemma not_of_mem_splitOnP {α : Type*} {p : α → Bool} :
    ∀ {t : List α} {w : List α}, w ∈ t.splitOnP p → ∀ c ∈ w, p c = false
  | [], w, hw => by simp [List.splitOnP_nil] at hw; subst hw; simp
  | x :: xs, w, hw => by
    rw [List.splitOnP_cons_eq_if_modifyHead] at hw
    split_ifs at hw with hx
    · rcases List.mem_cons.1 hw with rfl | hw
      · simp
      · exact not_of_mem_splitOnP hw
    · obtain ⟨r, rs, hr⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p xs)
      rw [hr, List.modifyHead_cons] at hw
      rcases List.mem_cons.1 hw with rfl | hw
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · simpa using hx
        · exact not_of_mem_splitOnP (hr ▸ List.mem_cons_self ..) c hc
      · exact not_of_mem_splitOnP (hr ▸ List.mem_cons_of_mem _ hw)

/-- A word is non-empty and contains no break. -/
lemma mem_words {t : Text} {w : Word} (h : w ∈ words t) :
    w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c := by
  obtain ⟨hw, hne⟩ := List.mem_filter.1 h
  exact ⟨by simpa using hne, fun c hc => by simpa using not_of_mem_splitOnP hw c hc⟩

/-- A text of breaks only has no words. -/
lemma words_eq_nil {t : Text} (h : ∀ c ∈ t, IsBreak c) : words t = [] := by
  rw [words_eq_book]; exact Book.words_of_forall_sep h

/-! ## Cuts

A layout of `ws` is a cut of `ws` into non-empty consecutive pieces, and a list
has finitely many cuts.  `cuts` lists them, which is what makes `Goal`
decidable. -/

/-- Every cut of a list into non-empty consecutive pieces. -/
private def cuts {α : Type*} : List α → List (List (List α))
  | [] => [[]]
  | a :: as => (cuts as).flatMap fun ls =>
      match ls with
      | [] => [[[a]]]
      | l :: ls' => [[a] :: l :: ls', (a :: l) :: ls']

private lemma mem_cuts {α : Type*} {ws : List α} {ls : List (List α)} :
    ls ∈ cuts ws ↔ [] ∉ ls ∧ ls.flatten = ws := by
  induction ws generalizing ls with
  | nil =>
    simp only [cuts, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, hf⟩
      rcases ls with _ | ⟨l, ls⟩
      · rfl
      · simp only [List.flatten_cons, List.append_eq_nil_iff] at hf
        exact absurd (hf.1 ▸ List.mem_cons_self ..) h
  | cons a as ih =>
    simp only [cuts, List.mem_flatMap]
    constructor
    · rintro ⟨ls₀, h₀, hls⟩
      obtain ⟨hne, hf⟩ := ih.1 h₀
      rcases ls₀ with _ | ⟨l, ls₀⟩
      · simp only [List.flatten_nil] at hf
        simp only [List.mem_singleton] at hls
        subst hls; subst hf; simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
        rcases hls with rfl | rfl
        · exact ⟨by simpa using hne, by simpa using hf⟩
        · refine ⟨?_, by simpa using hf⟩
          simp only [List.mem_cons, not_or] at hne ⊢
          exact ⟨by simp, hne.2⟩
    · rintro ⟨hne, hf⟩
      rcases ls with _ | ⟨_ | ⟨b, l⟩, ls⟩
      · simp at hf
      · exact absurd (List.mem_cons_self ..) hne
      · simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
        obtain ⟨rfl, hf⟩ := hf
        simp only [List.mem_cons, not_or] at hne
        rcases l with _ | ⟨c, l⟩
        · refine ⟨ls, ih.2 ⟨hne.2, by simpa using hf⟩, ?_⟩
          rcases ls with _ | ⟨l', ls⟩
          · simp
          · simp
        · refine ⟨(c :: l) :: ls, ih.2 ⟨?_, by simpa using hf⟩, by simp⟩
          simp only [List.mem_cons, not_or]
          exact ⟨by simp, hne.2⟩

/-! ## Decidability -/

/-- Whether `ls` lays `ws` out is decidable: each of its three conditions is. -/
instance (M : ℕ) (ws : List Word) (ls : List Line) : Decidable (Layout M ws ls) :=
  decidable_of_iff (ls.flatten = ws ∧ [] ∉ ls ∧ ∀ l ∈ ls, (renderLine l).length ≤ M)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- Every layout is a cut, so the quantifications in `Goal` are bounded. -/
private lemma goal_iff_cuts {M : ℕ} {i o : Text} :
    Goal M i o ↔ ∃ ls ∈ cuts (words i), Layout M (words i) ls ∧
      (∀ ls' ∈ cuts (words i), Layout M (words i) ls' → ls.length ≤ ls'.length) ∧
        o = render ls := by
  constructor
  · rintro ⟨ls, hl, hmin, rfl⟩
    exact ⟨ls, mem_cuts.2 ⟨hl.nonempty, hl.flatten⟩, hl, fun ls' _ hl' => hmin ls' hl', rfl⟩
  · rintro ⟨ls, -, hl, hmin, rfl⟩
    exact ⟨ls, hl, fun ls' hl' => hmin ls' (mem_cuts.2 ⟨hl'.nonempty, hl'.flatten⟩) hl',
      rfl⟩

/-- The specification is decidable.  The instance reduces in the kernel, so
`decide` settles concrete instances of `Goal`. -/
instance (M : ℕ) (i o : Text) : Decidable (Goal M i o) :=
  decidable_of_iff _ goal_iff_cuts.symm

/-! ## Rendering

The equations `renderLine` and `render` satisfy, and the two facts about a word
on a line that feasibility needs. -/

@[simp] private lemma renderLine_nil : renderLine [] = [] := rfl

@[simp] private lemma renderLine_singleton (w : Word) : renderLine [w] = w :=
  List.intercalate_singleton

private lemma renderLine_cons_cons (w w' : Word) (l : Line) :
    renderLine (w :: w' :: l) = w ++ blank :: renderLine (w' :: l) := by
  simp [renderLine, List.intercalate_cons_cons]

@[simp] private lemma render_nil : render [] = [] := rfl

@[simp] private lemma render_singleton (l : Line) : render [l] = renderLine l :=
  List.intercalate_singleton

private lemma render_cons_cons (l l' : Line) (ls : List Line) :
    render (l :: l' :: ls) = renderLine l ++ newline :: render (l' :: ls) := by
  simp [render, List.intercalate_cons_cons]

/-- A word is a stretch of the line it is printed on. -/
private lemma sublist_renderLine {w : Word} : ∀ {l : Line}, w ∈ l → w.Sublist (renderLine l)
  | [], h => by simp at h
  | [_], h => by rw [List.mem_singleton] at h; subst h; simp
  | _ :: _ :: _, h => by
    rw [renderLine_cons_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact (List.prefix_append _ _).sublist
    · exact (sublist_renderLine h).trans
        ((List.sublist_cons_self _ _).trans (List.sublist_append_right _ _))

/-- A word is no wider than the line it is printed on. -/
private lemma length_le_renderLine {w : Word} {l : Line} (h : w ∈ l) :
    w.length ≤ (renderLine l).length :=
  (sublist_renderLine h).length_le

/-! ## Feasibility -/

private lemma flatten_map_singleton {α : Type*} (ws : List α) :
    (ws.map fun w => [w]).flatten = ws := by
  induction ws <;> simp [*]

/-- One word per line is a layout exactly when every word fits.  This is the
book's `owpl`. -/
private lemma layout_map_singleton {M : ℕ} {ws : List Word} :
    Layout M ws (ws.map fun w => [w]) ↔ ∀ w ∈ ws, w.length ≤ M := by
  constructor
  · intro h w hw
    have := h.fits [w] (List.mem_map_of_mem hw)
    rwa [renderLine_singleton] at this
  · intro h
    refine ⟨flatten_map_singleton ws, by simp, ?_⟩
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ w hw rfl
    simpa using h w hw

/-- Among the layouts of `ws`, if there are any, some has fewest lines.  The
minimum exists because `ℕ` is well-ordered; `Meyer.Common.minSet_nonempty` is
the book's minimisation lemma. -/
private lemma exists_min_layout {M : ℕ} {ws : List Word} (h : ∃ ls, Layout M ws ls) :
    ∃ ls, Layout M ws ls ∧ ∀ ls', Layout M ws ls' → ls.length ≤ ls'.length := by
  obtain ⟨ls, hls, hmin⟩ := minSet_nonempty (X := {ls | Layout M ws ls}) List.length h
  exact ⟨ls, hls, hmin⟩

/-- **Feasibility.**  An input has an output exactly when each of its words fits
on a line.  This is the counterpart of the paper's domain theorem and of the
book's `T8`, stated on the words rather than through `max_line_length` or
`maxword`. -/
theorem feasibility (M : ℕ) (i : Text) :
    (∃ o, Goal M i o) ↔ ∀ w ∈ words i, w.length ≤ M := by
  constructor
  · rintro ⟨o, ls, hl, -, -⟩ w hw
    rw [← hl.flatten, List.mem_flatten] at hw
    obtain ⟨l, hl', hw⟩ := hw
    exact (length_le_renderLine hw).trans (hl.fits l hl')
  · intro h
    obtain ⟨ls, hls, hmin⟩ := exists_min_layout ⟨_, layout_map_singleton.2 h⟩
    exact ⟨render ls, ls, hls, hmin, rfl⟩

/-! ## Nondeterminism -/

/-- **The relation is not a function.**  Meyer's example from the book,
`␣␣ABC␣␣D␣␣EFG` at `M = 5`, has the two outputs he displays, and the paper's
`WHO WHAT WHEN` at `MAXPOS = 10` would do as well.  Both are settled by
`decide`. -/
theorem goal_not_functional :
    ∃ (M : ℕ) (i o₁ o₂ : Text), Goal M i o₁ ∧ Goal M i o₂ ∧ o₁ ≠ o₂ :=
  ⟨5, "  ABC  D  EFG".toList, "ABC D\nEFG".toList, "ABC\nD EFG".toList,
    by decide, by decide, by decide⟩

/-- The paper's example, for good measure. -/
example : Goal 10 "WHO WHAT WHEN".toList "WHO WHAT\nWHEN".toList ∧
    Goal 10 "WHO WHAT WHEN".toList "WHO\nWHAT WHEN".toList ∧
    ¬ Goal 10 "WHO WHAT WHEN".toList "WHO\nWHAT\nWHEN".toList := by
  decide

/-! ## An input of breaks only -/

/-- The counterpart of the book's `T7`: an input made of breaks only has exactly
one output, the empty text. -/
theorem goal_of_forall_isBreak {M : ℕ} {i : Text} (h : ∀ c ∈ i, IsBreak c) (o : Text) :
    Goal M i o ↔ o = [] := by
  rw [Goal, words_eq_nil h]
  constructor
  · rintro ⟨ls, hl, -, rfl⟩
    rcases ls with _ | ⟨l, ls⟩
    · rfl
    · have := hl.flatten
      simp only [List.flatten_cons, List.append_eq_nil_iff] at this
      exact absurd (this.1 ▸ List.mem_cons_self ..) hl.nonempty
  · rintro rfl
    refine ⟨[], ⟨rfl, by simp, by simp⟩, fun _ _ => Nat.zero_le _, rfl⟩

/-! ## The printed form of a cut

What `render` does to a cut of `w :: ws`: it prints `w`, then one separator, then
a cut of `ws`.  Everything about the length, the new lines and the longest line
of a printed cut follows from this one equation. -/

private lemma renderLine_cons_word (c : Char) (w : Word) (l : Line) :
    renderLine ((c :: w) :: l) = c :: renderLine (w :: l) := by
  rcases l with _ | ⟨w', l⟩
  · simp
  · simp [renderLine_cons_cons]

private lemma render_cons_word (c : Char) (w : Word) (l : Line) (ls : List Line) :
    render (((c :: w) :: l) :: ls) = c :: render ((w :: l) :: ls) := by
  rcases ls with _ | ⟨l', ls⟩
  · simp [renderLine_cons_word]
  · simp [render_cons_cons, renderLine_cons_word]

private lemma render_cons_blank (w w' : Word) (l : Line) (ls : List Line) :
    render ((w :: w' :: l) :: ls) = w ++ blank :: render ((w' :: l) :: ls) := by
  rcases ls with _ | ⟨l', ls⟩
  · simp [renderLine_cons_cons]
  · simp [render_cons_cons, renderLine_cons_cons]

private lemma render_cons_newline (w : Word) (l : Line) (ls : List Line) :
    render ([w] :: l :: ls) = w ++ newline :: render (l :: ls) := by
  simp [render_cons_cons]

/-- A cut of the empty list is empty. -/
private lemma eq_nil_of_cut {ls : List Line} (hne : [] ∉ ls) (hf : ls.flatten = []) :
    ls = [] := by
  rcases ls with _ | ⟨l, ls⟩
  · rfl
  · simp only [List.flatten_cons, List.append_eq_nil_iff] at hf
    exact absurd (hf.1 ▸ List.mem_cons_self ..) hne

/-- A cut of `w :: ws` is either the single line `[w]`, when `ws` is empty, or
prints as `w`, one separator, and a cut of `ws`. -/
private lemma render_cut_cons {w : Word} {ws : List Word} {ls : List Line}
    (hne : [] ∉ ls) (hf : ls.flatten = w :: ws) :
    (ws = [] ∧ ls = [[w]]) ∨
      ws ≠ [] ∧ ∃ s ls', IsBreak s ∧ [] ∉ ls' ∧ ls'.flatten = ws ∧
        render ls = w ++ s :: render ls' := by
  rcases ls with _ | ⟨_ | ⟨w', l⟩, ls⟩
  · simp at hf
  · exact absurd (List.mem_cons_self ..) hne
  · simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
    obtain ⟨rfl, hf⟩ := hf
    simp only [List.mem_cons, not_or] at hne
    rcases l with _ | ⟨w'', l⟩
    · rcases ls with _ | ⟨_ | ⟨w₁, l'⟩, ls⟩
      · exact Or.inl ⟨by simpa using hf, rfl⟩
      · exact absurd (List.mem_cons_self ..) hne.2
      · refine Or.inr ⟨?_, newline, (w₁ :: l') :: ls, Or.inr rfl, hne.2, by simpa using hf,
          render_cons_newline ..⟩
        simp only [List.nil_append, List.flatten_cons, List.cons_append] at hf
        rw [← hf]; simp
    · refine Or.inr ⟨by rw [← hf]; simp, blank, (w'' :: l) :: ls, Or.inl rfl, ?_,
        by simpa using hf, render_cons_blank ..⟩
      simp only [List.mem_cons, not_or]
      exact ⟨by simp, hne.2⟩

/-- A printed cut is as long as its letters plus one separator between
consecutive words: the bound `Meyer.Book.length_add_length_words_le` is attained. -/
private lemma length_render_cut : ∀ {ws : List Word} {ls : List Line}, ws ≠ [] → [] ∉ ls →
    ls.flatten = ws → (render ls).length + 1 = ws.flatten.length + ws.length
  | [], _, h, _, _ => absurd rfl h
  | w :: ws, ls, _, hne, hf => by
    rcases render_cut_cons hne hf with ⟨rfl, rfl⟩ | ⟨hws, s, ls', -, hne', hf', hr⟩
    · simp
    · have ih := length_render_cut hws hne' hf'
      rw [hr]
      simp only [List.length_append, List.length_cons, List.flatten_cons] at ih ⊢
      omega

/-- Two printed cuts of the same words differ only in their separators: they are
`EQUIVALENT` in the paper's sense. -/
private lemma forall₂_render_cut : ∀ {ws : List Word} {ls₁ ls₂ : List Line},
    [] ∉ ls₁ → ls₁.flatten = ws → [] ∉ ls₂ → ls₂.flatten = ws →
    List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) (render ls₁) (render ls₂)
  | [], _, _, h₁, hf₁, h₂, hf₂ => by
    rw [eq_nil_of_cut h₁ hf₁, eq_nil_of_cut h₂ hf₂]
    exact List.Forall₂.nil
  | w :: ws, ls₁, ls₂, h₁, hf₁, h₂, hf₂ => by
    have same : ∀ (t : Text) {a b : Text},
        List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) a b →
        List.Forall₂ (fun x y => x = y ∨ (IsBreak x ∧ IsBreak y)) (t ++ a) (t ++ b) := by
      intro t a b h
      induction t with
      | nil => exact h
      | cons c t ih => exact List.Forall₂.cons (Or.inl rfl) ih
    rcases render_cut_cons h₁ hf₁ with ⟨rfl, rfl⟩ |
      ⟨hws, s₁, ls₁', hs₁, hne₁, hf₁', hr₁⟩
    · rcases render_cut_cons h₂ hf₂ with ⟨-, rfl⟩ | ⟨hws, -⟩
      · exact List.forall₂_same.2 fun _ _ => Or.inl rfl
      · exact absurd rfl hws
    · rcases render_cut_cons h₂ hf₂ with ⟨rfl, -⟩ |
        ⟨-, s₂, ls₂', hs₂, hne₂, hf₂', hr₂⟩
      · exact absurd rfl hws
      · rw [hr₁, hr₂]
        exact same w (List.Forall₂.cons (Or.inr ⟨hs₁, hs₂⟩)
          (forall₂_render_cut hne₁ hf₁' hne₂ hf₂'))

/-! ## The words of a printed cut -/

/-- `Meyer.Book.words_append_sep`, for `words`. -/
private lemma words_append_break {c : Char} (hc : IsBreak c) (x y : Text) :
    words (x ++ c :: y) = words x ++ words y := by
  simp only [words_eq_book]; exact Book.words_append_sep hc x y

/-- A line of non-empty break-free words has exactly those words. -/
private lemma words_renderLine : ∀ {l : Line},
    (∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) → words (renderLine l) = l
  | [], _ => by simp [words, List.splitOnP_nil]
  | [w], h => by
    rw [renderLine_singleton, words_eq_book]
    exact Book.words_of_forall_letter (h w (by simp)).1 (h w (by simp)).2
  | w :: w' :: l, h => by
    rw [renderLine_cons_cons, words_append_break (Or.inl rfl),
      words_renderLine fun v hv => h v (List.mem_cons_of_mem _ hv), words_eq_book,
      Book.words_of_forall_letter (h w (by simp)).1 (h w (by simp)).2]
    rfl

/-- **Round trip.**  Printing a cut of non-empty break-free words and reading
the words back gives the words. -/
private lemma words_render : ∀ {ls : List Line},
    (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) →
    words (render ls) = ls.flatten
  | [], _ => by simp [words, List.splitOnP_nil]
  | [l], h => by rw [render_singleton, words_renderLine (h l (by simp))]; simp
  | l :: l' :: ls, h => by
    rw [render_cons_cons, words_append_break (Or.inr rfl), words_renderLine (h l (by simp)),
      words_render fun l'' hl'' => h l'' (List.mem_cons_of_mem _ hl'')]
    simp

/-! ## Shortest recasts are printed cuts

The book minimises length before anything else, and `[L]`, `[T]` and `[R]` each
shorten a text with a separator at an end or two separators side by side.  So a
shortest recast is a text of the kind the paper's `SINGLE_BREAKS` describes,
with the two ends bare as well, and such a text is the printed form of a cut of
its own words. -/

/-- A shortest recast has no two adjacent separators: `[R]` would shorten it.
In the paper's vocabulary, it satisfies `NoDoubleBreak`. -/
private lemma noDoubleBreak_of_mem_minRecasts {i o : Text} (ho : o ∈ Book.MinRecasts i) :
    Paper.NoDoubleBreak o := by
  obtain ⟨hor, homin⟩ := Book.mem_minRecasts_iff.1 ho
  refine List.isChain_iff_forall_rel_of_append_cons_cons.2 fun s s' x y h hs hs' => ?_
  have hstep : Book.Recast1 o (x ++ [s] ++ y) := by
    rw [h, show x ++ s :: s' :: y = x ++ [s, s'] ++ y by simp]
    exact Book.recast1_replace ⟨by simp, by simp [hs, hs']⟩ hs
  have := homin _ (Book.recast_trans hor (Book.recast_of_recast1 hstep))
  rw [h] at this
  simp at this
  omega

/-- A text with no two adjacent breaks and no break at either end is the printed
form of a cut into non-empty break-free words. -/
private lemma exists_cut_of_tight {o : Text} (hchain : Paper.NoDoubleBreak o)
    (hhead : ∀ c t, o = c :: t → ¬ IsBreak c)
    (hlast : ∀ t c, o = t ++ [c] → ¬ IsBreak c) :
    ∃ ls : List Line, [] ∉ ls ∧
      (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) ∧ o = render ls := by
  obtain ⟨n, hn⟩ : ∃ n, o.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing o with
  | _ n ih =>
  rw [Paper.NoDoubleBreak, List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
  rcases o with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · exact ⟨[], by simp, by simp, rfl⟩
  · exact ⟨[[[c]]], by simp, by simpa using hhead c [] rfl, by simp⟩
  · have hc : ¬ IsBreak c := hhead c _ rfl
    -- The induction hypothesis, applied to a proper tail that starts with a letter.
    have step : ∀ t : Text, t.length < n → (∀ c' t', t = c' :: t' → ¬ IsBreak c') →
        (∀ x s s' y, t = x ++ s :: s' :: y → IsBreak s → ¬ IsBreak s') →
        (∀ t' c', t = t' ++ [c'] → ¬ IsBreak c') →
        ∃ ls : List Line, [] ∉ ls ∧
          (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) ∧ t = render ls :=
      fun t ht hh hch hl => ih t.length ht (List.isChain_iff_forall_rel_of_append_cons_cons.2
        fun _ _ _ _ h => hch _ _ _ _ h) hh hl rfl
    -- A printed cut that is non-empty starts with a non-empty line and word.
    have shape : ∀ (ls : List Line) (t : Text), [] ∉ ls →
        (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) → t ≠ [] →
        t = render ls → ∃ w l ls', ls = (w :: l) :: ls' := by
      intro ls t hne hw ht hr
      rcases ls with _ | ⟨_ | ⟨w, l⟩, ls'⟩
      · exact absurd (hr ▸ render_nil) ht
      · exact absurd (List.mem_cons_self ..) hne
      · exact ⟨w, l, ls', rfl⟩
    by_cases hd : IsBreak d
    · -- `c d e …` with `d` a separator: `e` exists and is a letter.
      rcases rest with _ | ⟨e, rest⟩
      · exact absurd hd (hlast [c] d rfl)
      have he : ¬ IsBreak e := hchain (l₁ := [c]) (l₂ := rest) rfl hd
      obtain ⟨ls, hne, hw, hr⟩ := step (e :: rest)
        (by subst hn; simp only [List.length_cons]; omega)
        (fun c' t' h => by cases h; exact he)
        (fun x s s' y h => hchain (l₁ := c :: d :: x) (by rw [h]; rfl))
        (fun t' c' h => hlast (c :: d :: t') c' (by rw [h]; rfl))
      obtain ⟨w, l, ls', rfl⟩ := shape ls _ hne hw (by simp) hr
      rcases hd with rfl | rfl
      · refine ⟨([c] :: w :: l) :: ls', ?_, ?_, ?_⟩
        · simp only [List.mem_cons, not_or] at hne ⊢
          exact ⟨by simp, hne.2⟩
        · intro l₁ hl₁ v hv
          rcases List.mem_cons.1 hl₁ with rfl | hl₁
          · rcases List.mem_cons.1 hv with rfl | hv
            · exact ⟨by simp, by simpa using hc⟩
            · exact hw _ (List.mem_cons_self ..) v hv
          · exact hw l₁ (List.mem_cons_of_mem _ hl₁) v hv
        · rw [render_cons_blank, ← hr]; rfl
      · refine ⟨[[c]] :: (w :: l) :: ls', ?_, ?_, ?_⟩
        · simp only [List.mem_cons, not_or] at hne ⊢
          exact ⟨by simp, hne⟩
        · intro l₁ hl₁ v hv
          rcases List.mem_cons.1 hl₁ with rfl | hl₁
          · rw [List.mem_singleton] at hv; subst hv
            exact ⟨by simp, by simpa using hc⟩
          · exact hw l₁ hl₁ v hv
        · rw [render_cons_newline, ← hr]; rfl
    · -- `c d …` with `d` a letter: `d` joins the first word.
      obtain ⟨ls, hne, hw, hr⟩ := step (d :: rest)
        (by subst hn; simp only [List.length_cons]; omega)
        (fun c' t' h => by cases h; exact hd)
        (fun x s s' y h => hchain (l₁ := c :: x) (by rw [h]; rfl))
        (fun t' c' h => hlast (c :: t') c' (by rw [h]; rfl))
      obtain ⟨w, l, ls', rfl⟩ := shape ls _ hne hw (by simp) hr
      refine ⟨((c :: w) :: l) :: ls', ?_, ?_, ?_⟩
      · simp only [List.mem_cons, not_or] at hne ⊢
        exact ⟨by simp, hne.2⟩
      · intro l₁ hl₁ v hv
        rcases List.mem_cons.1 hl₁ with rfl | hl₁
        · rcases List.mem_cons.1 hv with rfl | hv
          · refine ⟨by simp, fun c' hc' => ?_⟩
            rcases List.mem_cons.1 hc' with rfl | hc'
            · exact hc
            · exact (hw _ (List.mem_cons_self ..) w (List.mem_cons_self ..)).2 c' hc'
          · exact hw _ (List.mem_cons_self ..) v (List.mem_cons_of_mem _ hv)
        · exact hw l₁ (List.mem_cons_of_mem _ hl₁) v hv
      · rw [render_cons_word, ← hr]

/-- **A shortest recast of `i` is a printed cut of the words of `i`.**  The cut is
of the words of the recast, which are the words of `i` by `T3`. -/
private lemma exists_cut_of_mem_minRecasts {i o : Text} (ho : o ∈ Book.MinRecasts i) :
    ∃ ls : List Line, [] ∉ ls ∧ ls.flatten = words i ∧ o = render ls := by
  obtain ⟨ls, hne, hw, rfl⟩ := exists_cut_of_tight (noDoubleBreak_of_mem_minRecasts ho)
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
  · rw [eq_nil_of_cut hne (hw ▸ hf)]; simp
  · have := length_render_cut hw hne hf
    omega

/-! ## Lines and new lines of a printed cut -/

/-- A line of break-free words contains no new line. -/
private lemma newline_not_mem_renderLine : ∀ {l : Line},
    (∀ w ∈ l, ∀ c ∈ w, ¬ IsBreak c) → newline ∉ renderLine l
  | [], _ => by simp
  | [w], h => by
    rw [renderLine_singleton]
    exact fun hc => h w (by simp) newline hc (Or.inr rfl)
  | w :: w' :: l, h => by
    rw [renderLine_cons_cons]
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨fun hc => h w (by simp) newline hc (Or.inr rfl), blank_ne_newline.symm,
      newline_not_mem_renderLine fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

/-- `new_lines` of a printed cut is one less than its number of lines. -/
private lemma newLines_render : ∀ {ls : List Line}, ls ≠ [] →
    (∀ l ∈ ls, newline ∉ renderLine l) → Book.newLines (render ls) + 1 = ls.length
  | [], h, _ => absurd rfl h
  | [l], _, h => by
    rw [render_singleton, Book.newLines, List.count_eq_zero_of_not_mem (h l (by simp))]; rfl
  | l :: l' :: ls, _, h => by
    have ih := newLines_render (List.cons_ne_nil l' ls)
      fun l'' hl'' => h l'' (List.mem_cons_of_mem _ hl'')
    rw [render_cons_cons, Book.newLines, List.count_append,
      List.count_eq_zero_of_not_mem (h l (by simp)), List.count_cons_self]
    rw [Book.newLines] at ih
    simp only [List.length_cons] at ih ⊢
    omega

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

/-- **The book's specification is this one.**  `Goal M i o ↔ Meyer.Book.Goal M i o`.

Reading the book's `S1` through the lemmas above: its shortest recasts are the
printed cuts of the words of the input; `maxline ≤ M` on a printed cut says that
every line fits; and `new_lines` counts the lines less one.  So minimising
`new_lines` over the shortest recasts with `maxline ≤ M` is minimising the
number of lines over the layouts, and `S1` and `Goal` accept the same
outputs. -/
theorem goal_iff_book (M : ℕ) (i o : Text) : Goal M i o ↔ Book.Goal M i o := by
  have hwords : ∀ ls : List Line, ls.flatten = words i →
      ∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c :=
    fun ls hf l hl w hw => mem_words (hf ▸ List.mem_flatten.2 ⟨l, hl, hw⟩)
  have hnl : ∀ ls : List Line, ls.flatten = words i → ∀ l ∈ ls, newline ∉ renderLine l :=
    fun ls hf l hl => newline_not_mem_renderLine fun w hw => (hwords ls hf l hl w hw).2
  rw [Book.Goal, Book.mem_solutions_iff]
  constructor
  · rintro ⟨ls, hl, hmin, rfl⟩
    refine ⟨⟨render_mem_minRecasts hl.nonempty hl.flatten,
      (maxLine_render_le_iff (hnl ls hl.flatten)).2 hl.fits⟩, fun y hy hmy => ?_⟩
    obtain ⟨ls', hne', hf', rfl⟩ := exists_cut_of_mem_minRecasts hy
    have hlen := hmin ls' ⟨hf', hne', (maxLine_render_le_iff (hnl ls' hf')).1 hmy⟩
    rcases ls with _ | ⟨l, ls⟩
    · simp [Book.newLines]
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

/-- **The paper's specification is a different one.**  On the separating input of
`Meyer.Comparison.specifications_differ`, `␣AB` at a line limit of two, each of
the two relations accepts an output the other rejects. -/
theorem goal_ne_paper :
    ∃ (M : ℕ) (i o₁ o₂ : Text),
      Paper.Goal M i o₁ ∧ ¬ Goal M i o₁ ∧ Goal M i o₂ ∧ ¬ Paper.Goal M i o₂ := by
  obtain ⟨M, i, o₁, o₂, h₁, h₁', h₂, h₂'⟩ := Comparison.specifications_differ
  exact ⟨M, i, o₁, o₂, h₁, fun h => h₁' ((goal_iff_book M i o₁).1 h),
    (goal_iff_book M i o₂).2 h₂, h₂'⟩

/-- The book's `T8` in the book's own terms, transferred: an output exists exactly
when `maxword (in) ≤ M`. -/
lemma feasibility_maxWord (M : ℕ) (i : Text) : (∃ o, Goal M i o) ↔ Book.maxWord i ≤ M := by
  rw [← Book.feasibility]
  exact exists_congr fun o => goal_iff_book M i o

end

end Native
