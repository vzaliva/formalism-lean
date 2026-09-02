import Native.Spec
import Mathlib.Data.List.Forall2

/-!
# Properties of the Lean-native specification

What can be said about `Native.ByLayout` on its own, without reference to either of
Meyer's specifications.  `Native.Comparison` does the comparing.

* **Decidability.**  A layout of a finite list of words is one of finitely many
  cuts of that list, so `Layout` and `ByLayout` are decidable and concrete claims are
  settled by `decide`.  The specification stays a proposition; that it can be
  evaluated is a theorem about it, not part of it.
* **Feasibility**, `feasibility`: an input has an output exactly when each of
  its words fits on a line.
* **Nondeterminism**, `byLayout_not_functional`, on Meyer's own example.
* **The two formulations agree**, `byLayout_eq_byText`: `ByLayout`, by way of
  layouts, and `ByText`, on the output text, are the same relation.  An
  acceptable text is parsed back into a layout by `List.splitOn`, and
  `List.intercalate_splitOn` says printing that layout gives the text back.
  `byText_iff_minSet` puts `ByText` in the shape of Meyer's specifications,
  and decidability passes from `ByLayout` to `ByText` through the equivalence.
* **The length of an output**, `length_of_byLayout`: the book's `T1` sharpened to
  an equation, a consequence of the three conditions of `Acceptable`.

The machinery is a handful of equations for `render` on a *cut* of a list of
words, a list of lines `ls` with `[] ∉ ls` and `ls.flatten = ws`, and their
inverses: `words` reads the words back from a printed cut (`words_render`) and
`List.splitOn` reads the lines back (`splitOn_render`).  The lemmas about
printed cuts that `Native.Comparison` builds on are public; the rest is
private.
-/

namespace Native

open Meyer

noncomputable section

/-! ## Words -/

@[simp] private lemma words_nil : words [] = [] := by simp [words, List.splitOnP_nil]

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
private lemma mem_words {t : Text} {w : Word} (h : w ∈ words t) :
    w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c := by
  obtain ⟨hw, hne⟩ := List.mem_filter.1 h
  exact ⟨by simpa using hne, fun c hc => by simpa using not_of_mem_splitOnP hw c hc⟩

/-- **Words split at a break.**  Everything about `words` follows from this one
equation. -/
private lemma words_append_break {c : Char} (hc : IsBreak c) (x y : Text) :
    words (x ++ c :: y) = words x ++ words y := by
  unfold words
  rw [List.splitOnP_append_cons x y (by simpa using hc), List.filter_append]

/-- A break at the front of a text belongs to no word. -/
private lemma words_cons_break {c : Char} (hc : IsBreak c) (t : Text) :
    words (c :: t) = words t := by
  simpa using words_append_break hc [] t

/-- A text of breaks only has no words. -/
private lemma words_eq_nil {t : Text} (h : ∀ c ∈ t, IsBreak c) : words t = [] := by
  induction t with
  | nil => exact words_nil
  | cons c t ih =>
    rw [words_cons_break (h c (List.mem_cons_self ..))]
    exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- A non-empty text with no break in it is one word. -/
private lemma words_of_forall_letter {w : Text} (hne : w ≠ []) (h : ∀ c ∈ w, ¬ IsBreak c) :
    words w = [w] := by
  rw [words, List.splitOnP_eq_singleton fun c hc => by simpa using h c hc]
  simp [hne]

/-- The words carried by a cut of `words i` are non-empty and break-free. -/
lemma words_of_cut {i : Text} {ls : List Line} (hf : ls.flatten = words i) :
    ∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c :=
  fun l hl _ hw => mem_words (hf ▸ List.mem_flatten.2 ⟨l, hl, hw⟩)

/-! ## Cuts

A layout of `ws` is a cut of `ws` into non-empty consecutive pieces, and a list
has finitely many cuts.  `cuts` lists them, which is what makes `ByLayout`
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

/-- Every layout is a cut, so the quantifications in `ByLayout` are bounded. -/
private lemma byLayout_iff_cuts {M : ℕ} {i o : Text} :
    ByLayout M i o ↔ ∃ ls ∈ cuts (words i), Layout M (words i) ls ∧
      (∀ ls' ∈ cuts (words i), Layout M (words i) ls' → ls.length ≤ ls'.length) ∧
        o = render ls := by
  constructor
  · rintro ⟨ls, hl, hmin, rfl⟩
    exact ⟨ls, mem_cuts.2 ⟨hl.nonempty, hl.flatten⟩, hl, fun ls' _ hl' => hmin ls' hl', rfl⟩
  · rintro ⟨ls, -, hl, hmin, rfl⟩
    exact ⟨ls, hl, fun ls' hl' => hmin ls' (mem_cuts.2 ⟨hl'.nonempty, hl'.flatten⟩) hl',
      rfl⟩

/-- The specification is decidable.  The instance reduces in the kernel, so
`decide` settles concrete instances of `ByLayout`. -/
instance (M : ℕ) (i o : Text) : Decidable (ByLayout M i o) :=
  decidable_of_iff _ byLayout_iff_cuts.symm

/-! ## Printing

The equations `renderLine` and `render` satisfy. -/

/-- Used by `simp` in the base cases below. -/
@[simp] private lemma renderLine_nil : renderLine [] = [] := rfl

@[simp] private lemma renderLine_singleton (w : Word) : renderLine [w] = w :=
  List.intercalate_singleton

private lemma renderLine_cons_cons (w w' : Word) (l : Line) :
    renderLine (w :: w' :: l) = w ++ blank :: renderLine (w' :: l) := by
  simp [renderLine, List.intercalate_cons_cons]

private lemma renderLine_cons_word (c : Char) (w : Word) (l : Line) :
    renderLine ((c :: w) :: l) = c :: renderLine (w :: l) := by
  rcases l with _ | ⟨w', l⟩
  · simp
  · simp [renderLine_cons_cons]

/-- Printing the empty layout gives the empty text. -/
@[simp] lemma render_nil : render [] = [] := rfl

/-- A one-line layout prints as its line. -/
@[simp] lemma render_singleton (l : Line) : render [l] = renderLine l :=
  List.intercalate_singleton

/-- The first line, a new line, and the rest. -/
lemma render_cons_cons (l l' : Line) (ls : List Line) :
    render (l :: l' :: ls) = renderLine l ++ newline :: render (l' :: ls) := by
  simp [render, List.intercalate_cons_cons]

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

/-- A non-empty line of non-empty words prints as a non-empty text. -/
private lemma renderLine_ne_nil :
    ∀ {l : Line}, l ≠ [] → (∀ w ∈ l, w ≠ []) → renderLine l ≠ []
  | [], h, _ => absurd rfl h
  | [w], _, h => by rw [renderLine_singleton]; exact h w (by simp)
  | _ :: _ :: _, _, _ => by rw [renderLine_cons_cons]; simp

/-- A line of break-free words contains no new line. -/
lemma newline_not_mem_renderLine : ∀ {l : Line},
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

/-- The new lines of a printed layout are its line breaks: one fewer than the
lines. -/
lemma count_newline_render : ∀ {ls : List Line}, ls ≠ [] →
    (∀ l ∈ ls, newline ∉ renderLine l) → (render ls).count newline + 1 = ls.length
  | [], h, _ => absurd rfl h
  | [l], _, h => by rw [render_singleton, List.count_eq_zero_of_not_mem (h l (by simp))]; rfl
  | l :: l' :: ls, _, h => by
    have ih := count_newline_render (List.cons_ne_nil l' ls)
      fun l'' hl'' => h l'' (List.mem_cons_of_mem _ hl'')
    rw [render_cons_cons, List.count_append, List.count_eq_zero_of_not_mem (h l (by simp)),
      List.count_cons_self]
    simp only [List.length_cons] at ih ⊢
    omega

/-! ## Printed cuts

What `render` does to a cut of `w :: ws`: it prints `w`, then one separator, then
a cut of `ws`.  Everything about the length and the words of a printed cut
follows from this one equation. -/

/-- A cut of the empty list is empty. -/
lemma eq_nil_of_cut {ls : List Line} (hne : [] ∉ ls) (hf : ls.flatten = []) : ls = [] := by
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
consecutive words. -/
lemma length_render_cut : ∀ {ws : List Word} {ls : List Line}, ws ≠ [] → [] ∉ ls →
    ls.flatten = ws → (render ls).length + 1 = ws.flatten.length + ws.length
  | [], _, h, _, _ => absurd rfl h
  | w :: ws, ls, _, hne, hf => by
    rcases render_cut_cons hne hf with ⟨rfl, rfl⟩ | ⟨hws, s, ls', -, hne', hf', hr⟩
    · simp
    · have ih := length_render_cut hws hne' hf'
      rw [hr]
      simp only [List.length_append, List.length_cons, List.flatten_cons] at ih ⊢
      omega

/-- Two printed cuts of the same words differ only in their separators. -/
lemma forall₂_render_cut : ∀ {ws : List Word} {ls₁ ls₂ : List Line},
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

/-! ## Reading a printed cut back

`words` recovers the words of a printed cut, and `List.splitOn` recovers its
lines and, from a line, its words. -/

/-- A line of non-empty break-free words has exactly those words. -/
private lemma words_renderLine : ∀ {l : Line},
    (∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) → words (renderLine l) = l
  | [], _ => by simp
  | [w], h => by
    rw [renderLine_singleton]
    exact words_of_forall_letter (h w (by simp)).1 (h w (by simp)).2
  | w :: w' :: l, h => by
    rw [renderLine_cons_cons, words_append_break (Or.inl rfl),
      words_renderLine fun v hv => h v (List.mem_cons_of_mem _ hv),
      words_of_forall_letter (h w (by simp)).1 (h w (by simp)).2]
    rfl

/-- **Round trip.**  Printing a cut of non-empty break-free words and reading
the words back gives the words. -/
lemma words_render : ∀ {ls : List Line},
    (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) →
    words (render ls) = ls.flatten
  | [], _ => by simp
  | [l], h => by rw [render_singleton, words_renderLine (h l (by simp))]; simp
  | l :: l' :: ls, h => by
    rw [render_cons_cons, words_append_break (Or.inr rfl), words_renderLine (h l (by simp)),
      words_render fun l'' hl'' => h l'' (List.mem_cons_of_mem _ hl'')]
    simp

/-- `List.splitOn` reads the lines back from a printed layout. -/
private lemma splitOn_render {ls : List Line} (hne : ls ≠ [])
    (h : ∀ l ∈ ls, newline ∉ renderLine l) :
    (render ls).splitOn newline = ls.map renderLine :=
  List.splitOn_intercalate newline (by simpa using h) (by simpa using hne)

/-- `List.splitOn` reads the words back from a printed line. -/
private lemma splitOn_renderLine {l : Line} (hne : l ≠ []) (h : ∀ w ∈ l, blank ∉ w) :
    (renderLine l).splitOn blank = l :=
  List.splitOn_intercalate blank h hne

/-- No piece of a split contains the character that was split on. -/
private lemma not_mem_of_mem_splitOn {xs w : Text} {x : Char} (h : w ∈ xs.splitOn x) :
    x ∉ w := by
  rw [List.splitOn_eq_splitOnP] at h
  intro hx
  simpa using not_of_mem_splitOnP h x hx

/-- The lines of a text and, on each line, its words, as `List.splitOn` reads
them.  On a well-formed text this inverts `render`. -/
private def parse (o : Text) : List Line :=
  (o.splitOn newline).map (·.splitOn blank)

private lemma renderLine_splitOn (line : Text) : renderLine (line.splitOn blank) = line :=
  List.intercalate_splitOn blank

/-- Printing what `List.splitOn` read gives the text back, for every text. -/
private lemma render_parse (o : Text) : render (parse o) = o := by
  unfold render parse
  rw [List.map_map, show (renderLine ∘ fun l : Text => l.splitOn blank) = id from
    funext fun l => renderLine_splitOn l, List.map_id]
  exact List.intercalate_splitOn newline

/-- `List.splitOn` reads one more line than there are new lines. -/
private lemma length_splitOn_newline (o : Text) :
    o.count newline + 1 = (o.splitOn newline).length := by
  have h := count_newline_render (ls := parse o) (by simp [parse, List.splitOn_ne_nil])
    fun l hl => by
      obtain ⟨line, hline, rfl⟩ := List.mem_map.1 hl
      rw [renderLine_splitOn]
      exact not_mem_of_mem_splitOn hline
  rw [render_parse] at h
  simpa [parse] using h

/-- **Parsing.**  A text with no two adjacent breaks and no break at either end
is the printed form of a cut into non-empty break-free words.  Strong induction
on the length: the text is a letter followed by either more letters, which join
the first word, or one separator and a text of the same kind. -/
lemma exists_cut_of_tight {o : Text}
    (hchain : ∀ x s s' y, o = x ++ s :: s' :: y → IsBreak s → ¬ IsBreak s')
    (hhead : ∀ c t, o = c :: t → ¬ IsBreak c)
    (hlast : ∀ t c, o = t ++ [c] → ¬ IsBreak c) :
    ∃ ls : List Line, [] ∉ ls ∧
      (∀ l ∈ ls, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c) ∧ o = render ls := by
  obtain ⟨n, hn⟩ : ∃ n, o.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing o with
  | _ n ih =>
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
      fun t ht hh hch hl => ih t.length ht hch hh hl rfl
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
      have he : ¬ IsBreak e := hchain [c] d e rest rfl hd
      obtain ⟨ls, hne, hw, hr⟩ := step (e :: rest)
        (by subst hn; simp only [List.length_cons]; omega)
        (fun c' t' h => by cases h; exact he)
        (fun x s s' y h => hchain (c :: d :: x) s s' y (by rw [h]; rfl))
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
        (fun x s s' y h => hchain (c :: x) s s' y (by rw [h]; rfl))
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
    (∃ o, ByLayout M i o) ↔ ∀ w ∈ words i, w.length ≤ M := by
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
theorem byLayout_not_functional :
    ∃ (M : ℕ) (i o₁ o₂ : Text), ByLayout M i o₁ ∧ ByLayout M i o₂ ∧ o₁ ≠ o₂ :=
  ⟨5, "  ABC  D  EFG".toList, "ABC D\nEFG".toList, "ABC\nD EFG".toList,
    by decide, by decide, by decide⟩

/-- The paper's example, for good measure. -/
example : ByLayout 10 "WHO WHAT WHEN".toList "WHO WHAT\nWHEN".toList ∧
    ByLayout 10 "WHO WHAT WHEN".toList "WHO\nWHAT WHEN".toList ∧
    ¬ ByLayout 10 "WHO WHAT WHEN".toList "WHO\nWHAT\nWHEN".toList := by
  decide

/-! ## An input of breaks only -/

/-- The counterpart of the book's `T7`: an input made of breaks only has exactly
one output, the empty text. -/
theorem byLayout_of_forall_isBreak {M : ℕ} {i : Text} (h : ∀ c ∈ i, IsBreak c) (o : Text) :
    ByLayout M i o ↔ o = [] := by
  rw [ByLayout, words_eq_nil h]
  constructor
  · rintro ⟨ls, hl, -, rfl⟩
    rw [eq_nil_of_cut hl.nonempty hl.flatten, render_nil]
  · rintro rfl
    exact ⟨[], ⟨rfl, by simp, by simp⟩, fun _ _ => Nat.zero_le _, rfl⟩

/-! ## The two formulations agree

Each output of `ByLayout` is `render ls` for a layout `ls` of the words of the
input, and the three conditions of `Acceptable` are read off that.  `fewestLines`
and the converse need the other direction: an acceptable text is
`render (parse o)` for a layout `parse o`, and its new lines count its lines. -/

/-- The lines of a printed layout are non-empty and fit. -/
private lemma linesFit_render {M : ℕ} {i : Text} {ls : List Line} (hl : Layout M (words i) ls) :
    (render ls) ≠ [] → ∀ l ∈ (render ls).splitOn newline, l ≠ [] ∧ l.length ≤ M := by
  intro ho l hl'
  have hw := words_of_cut hl.flatten
  have hne : ls ≠ [] := by rintro rfl; exact ho rfl
  rw [splitOn_render hne fun l hl => newline_not_mem_renderLine fun w hw' => (hw l hl w hw').2]
    at hl'
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl'
  exact ⟨renderLine_ne_nil (fun h => hl.nonempty (h ▸ hl₀))
    fun w hw' => (hw l₀ hl₀ w hw').1, hl.fits l₀ hl₀⟩

/-- The lines of a printed layout have one blank between words and none at the
ends. -/
private lemma singleBlanks_render {M : ℕ} {i : Text} {ls : List Line}
    (hl : Layout M (words i) ls) :
    (render ls) ≠ [] → ∀ l ∈ (render ls).splitOn newline, [] ∉ l.splitOn blank := by
  intro ho l hl'
  have hw := words_of_cut hl.flatten
  have hne : ls ≠ [] := by rintro rfl; exact ho rfl
  rw [splitOn_render hne fun l hl => newline_not_mem_renderLine fun w hw' => (hw l hl w hw').2]
    at hl'
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl'
  rw [splitOn_renderLine (fun h => hl.nonempty (h ▸ hl₀))
    fun w hw' hb => (hw l₀ hl₀ w hw').2 blank hb (Or.inl rfl)]
  exact fun h => (hw l₀ hl₀ [] h).1 rfl

/-- **A printed layout is acceptable**: the three conditions hold of `render ls` for
every layout `ls` of the words of `i`, minimal or not. -/
private lemma Layout.acceptable {M : ℕ} {i : Text} {ls : List Line}
    (hl : Layout M (words i) ls) : Acceptable M i (render ls) :=
  ⟨linesFit_render hl, singleBlanks_render hl,
    (words_render (words_of_cut hl.flatten)).trans hl.flatten⟩

/-- **An acceptable text is a printed layout**: what `List.splitOn` reads off a
non-empty acceptable text is a layout of the words of the input. -/
private lemma Acceptable.Fields.layout_parse {M : ℕ} {i o : Text} (h : Acceptable M i o)
    (ho : o ≠ []) : Layout M (words i) (parse o) := by
  have hw : ∀ l ∈ parse o, ∀ w ∈ l, w ≠ [] ∧ ∀ c ∈ w, ¬ IsBreak c := by
    intro l hl w hw
    obtain ⟨line, hline, rfl⟩ := List.mem_map.1 hl
    refine ⟨fun h' => h.singleBlanks ho line hline (h' ▸ hw), fun c hc hb => ?_⟩
    rcases hb with rfl | rfl
    · exact not_mem_of_mem_splitOn hw hc
    · have := (sublist_renderLine hw).subset hc
      rw [renderLine_splitOn] at this
      exact not_mem_of_mem_splitOn hline this
  refine ⟨?_, ?_, ?_⟩
  · rw [← words_render hw, render_parse]; exact h.sameWords
  · simp only [parse, List.mem_map, not_exists, not_and]
    exact fun line _ h => List.splitOn_ne_nil blank line h
  · intro l hl
    obtain ⟨line, hline, rfl⟩ := List.mem_map.1 hl
    rw [renderLine_splitOn]
    exact (h.linesFit ho line hline).2

/-- The new lines of a printed layout of the words of `i` count its lines. -/
private lemma count_newline_render_of_layout {M : ℕ} {i : Text} {l : Line} {ls : List Line}
    (hl : Layout M (words i) (l :: ls)) : (render (l :: ls)).count newline + 1 = (l :: ls).length :=
  count_newline_render (List.cons_ne_nil l ls) fun l' hl' =>
    newline_not_mem_renderLine fun w hw => (words_of_cut hl.flatten l' hl' w hw).2

/-- An output of `ByLayout` is one of `ByText`: acceptable, and with no more
lines than any acceptable text. -/
private lemma ByLayout.byText {M : ℕ} {i o : Text} (h : ByLayout M i o) : ByText M i o := by
  obtain ⟨ls, hl, hmin, rfl⟩ := h
  refine ⟨hl.acceptable, fun o' h' => ?_⟩
  rcases eq_or_ne o' [] with rfl | ho'
  · have hw : words i = [] := by rw [← h'.sameWords]; exact words_nil
    simp [eq_nil_of_cut hl.nonempty (hl.flatten.trans hw)]
  · have hlen := hmin (parse o') (h'.layout_parse ho')
    have h'' := length_splitOn_newline o'
    have hp : (parse o').length = (o'.splitOn newline).length := List.length_map ..
    rcases ls with _ | ⟨l, ls⟩
    · simp
    · have hc := count_newline_render_of_layout hl
      omega

/-- An output of `ByText` is one of `ByLayout`: the layout `List.splitOn` reads
off it has no more lines than any layout. -/
private lemma ByText.byLayout {M : ℕ} {i o : Text} (h : ByText M i o) : ByLayout M i o := by
  rcases eq_or_ne o [] with rfl | ho
  · have hw : words i = [] := by rw [← h.sameWords]; exact words_nil
    exact ⟨[], ⟨by rw [hw]; rfl, by simp, by simp⟩, fun _ _ => Nat.zero_le _, rfl⟩
  · have hp := h.layout_parse ho
    refine ⟨parse o, hp, fun ls' hl' => ?_, (render_parse o).symm⟩
    have hc := h.fewestLines (render ls') hl'.acceptable
    have h' := length_splitOn_newline o
    have hlen : (parse o).length = (o.splitOn newline).length := List.length_map ..
    rcases ls' with _ | ⟨l, ls'⟩
    · have hw : words i = [] := by simpa using hl'.flatten.symm
      have := eq_nil_of_cut hp.nonempty (hp.flatten.trans hw)
      simp [parse, List.splitOn_ne_nil] at this
    · have hc' := count_newline_render_of_layout hl'
      omega

/-- Pointwise: an output of `ByLayout` is an acceptable text with fewest lines,
and conversely. -/
private lemma byLayout_iff_byText {M : ℕ} {i o : Text} : ByLayout M i o ↔ ByText M i o :=
  ⟨ByLayout.byText, ByText.byLayout⟩

/-- **The two specifications are one relation.**  `ByLayout M` and `ByText M` are
equal as relations between input and output.  The book's `T1` to `T8` admit no
such theorem: the `M3`-defective reading of `S1` is provably a different
relation (`Meyer.Book.Bug.goal_unfilled`) and, by the argument in `README.md`,
has all eight. -/
theorem byLayout_eq_byText (M : ℕ) : ByLayout M = ByText M :=
  funext fun _ => funext fun _ => propext byLayout_iff_byText

/-- **`ByText` has the shape of Meyer's specifications**: it is `MIN_SET` of the
acceptable texts under the number of new lines, as the paper's `goal` is
`FEWEST_LINES (TRANSF (i))`, that is `MIN_SET (TRANSF (i), number_of_new_lines)`. -/
theorem byText_iff_minSet {M : ℕ} {i o : Text} :
    ByText M i o ↔ o ∈ MinSet {o' | Acceptable M i o'} (List.count newline) :=
  ⟨fun h => ⟨h.toFields, fun _ h' => h.fewestLines _ h'⟩,
    fun ⟨h, hmin⟩ => ⟨h, fun _ h' => hmin _ h'⟩⟩

/-! ## Decidability of the text formulation

`Acceptable` is a bounded condition and decidable outright.  `ByText`
quantifies over all texts and is not; it becomes decidable through
`byLayout_iff_byText`, which is the layout formulation doing work for the text
one. -/

/-- `Acceptable` is decidable: each of the three conditions is bounded. -/
instance (M : ℕ) (i o : Text) : Decidable (Acceptable M i o) :=
  decidable_of_iff ((o ≠ [] → ∀ l ∈ o.splitOn newline, l ≠ [] ∧ l.length ≤ M) ∧
      (o ≠ [] → ∀ l ∈ o.splitOn newline, [] ∉ l.splitOn blank) ∧ words o = words i)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- `ByText` is decidable, by way of the layouts. -/
instance (M : ℕ) (i o : Text) : Decidable (ByText M i o) :=
  decidable_of_iff _ byLayout_iff_byText

/-- Meyer's example, settled on the text formulation. -/
example : ByText 5 "  ABC  D  EFG".toList "ABC D\nEFG".toList ∧
    ¬ ByText 5 "  ABC  D  EFG".toList "ABC\nD\nEFG".toList := by
  decide

/-! ## The length of an output -/

/-- **The length of an output**: exactly the letters of the input plus one
separator per gap between words.  This is the book's `T1` sharpened to an
equation.  It is not a field of `Acceptable` because it follows from the three
that are -- an acceptable text is a printed layout, `Acceptable.Fields.layout_parse`,
and `length_render_cut` measures one -- and so detects nothing they do not. -/
theorem length_of_byLayout {M : ℕ} {i o : Text} (h : ByLayout M i o) (hw : words i ≠ []) :
    o.length + 1 = ((words i).map List.length).sum + (words i).length := by
  obtain ⟨ls, hl, -, rfl⟩ := h
  rw [← List.length_flatten]
  exact length_render_cut hw hl.nonempty hl.flatten

end

end Native
