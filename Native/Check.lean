import Native.Properties

/-!
# Deciding the 2022 specification

`Native.Properties` makes `ByLayout` decidable by enumerating the cuts of the
list of words, `2 ^ (n - 1)` of them for `n` words, which is out of reach at the
size of Naur's own example sentence.  This module gives a function
`check M i o : Bool` that runs in time linear in the texts and proves that it
decides `ByLayout`, `check_eq_true_iff`.  Nothing here depends on Meyer's
specifications; `Native.Comparison` carries the checker over to the book's `S1`.

It is the counterpart of `Meyer.Paper.Check` for the 1985 specification, and
simpler, because a layout is already a list of lines of words.

## How

`fill M ws` lays the words `ws` out line by line: each line takes as many of
the following words as fit.  It is a layout whenever each word fits on a line
(`layout_fill`), and no layout has fewer lines (`length_fill_le`).  The second
is the usual exchange argument: the first line of any layout is a prefix of the
words that fits, the greedy first line is the longest such prefix, and what is
left after a longer first line has a layout with no more lines
(`exists_layout_of_append`).

`check M i o` asks that `o` be acceptable (`Native.Acceptable`, which is
decidable outright) and have no more new lines than the printed greedy layout.
Acceptable texts are the printed layouts and their new lines count the lines
less one, so that is `ByText`, which is `ByLayout`.

`fill` is a word wrap.  It is here to compute the fewest lines, which deciding
the specification needs.
-/

namespace Native

open Meyer

/-! ## The greedy fill -/

/-- The width a list of words adds to a line that already holds something: each
word and the blank before it. -/
def tailWidth (l : List Word) : ℕ :=
  (l.map fun w => w.length + 1).sum

/-- `takeLine M k ws`: the words at the front of `ws` that still fit on a line of
width `M` already holding `k` characters, and the words after them. -/
def takeLine (M : ℕ) : ℕ → List Word → List Word × List Word
  | _, [] => ([], [])
  | k, w :: ws =>
    if k + 1 + w.length ≤ M then
      let r := takeLine M (k + 1 + w.length) ws
      (w :: r.1, r.2)
    else ([], w :: ws)

/-- `fill` with fuel: each line takes its first word and then what `takeLine`
gives it.  The fuel is the number of words, so it never runs out. -/
def fillAux (M : ℕ) : ℕ → List Word → List Line
  | 0, _ => []
  | _, [] => []
  | n + 1, w :: ws =>
    let r := takeLine M w.length ws
    (w :: r.1) :: fillAux M n r.2

/-- `fill M ws`: the words `ws` laid out line by line, greedily. -/
def fill (M : ℕ) (ws : List Word) : List Line :=
  fillAux M ws.length ws

/-- **The checker.**  `o` is acceptable and has no more new lines than the
greedy layout of the words of `i`.  `check_eq_true_iff`. -/
def check (M : ℕ) (i o : Text) : Bool :=
  decide (Acceptable M i o) &&
    decide (o.count newline ≤ (render (fill M (words i))).count newline)

/-! ## `takeLine` -/

/-- A line is printed as its first word and, for each further word, a blank and
the word. -/
private lemma length_renderLine_cons (w : Word) (l : List Word) :
    (renderLine (w :: l)).length = w.length + tailWidth l := by
  induction l generalizing w with
  | nil => simp [renderLine, tailWidth]
  | cons u l ih =>
    rw [renderLine, List.intercalate_cons_cons, ← renderLine]
    simp only [List.length_append, List.length_singleton, ih, tailWidth, List.map_cons,
      List.sum_cons]
    omega

private lemma takeLine_append (M : ℕ) :
    ∀ (k : ℕ) (ws : List Word), (takeLine M k ws).1 ++ (takeLine M k ws).2 = ws
  | _, [] => rfl
  | k, w :: ws => by
    unfold takeLine
    split_ifs
    · simp [takeLine_append M _ ws]
    · rfl

/-- What `takeLine` takes fits. -/
private lemma tailWidth_takeLine_le (M : ℕ) :
    ∀ (k : ℕ) (ws : List Word), k ≤ M → k + tailWidth (takeLine M k ws).1 ≤ M
  | k, [], hk => by simpa [takeLine, tailWidth] using hk
  | k, w :: ws, hk => by
    unfold takeLine
    split_ifs with h
    · have := tailWidth_takeLine_le M (k + 1 + w.length) ws h
      simp only [tailWidth, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simpa [tailWidth] using hk

/-- `takeLine` takes at least as much as any prefix that fits. -/
private lemma length_le_takeLine (M : ℕ) :
    ∀ (k : ℕ) (ws l r : List Word), ws = l ++ r → k + tailWidth l ≤ M →
      l.length ≤ (takeLine M k ws).1.length
  | _, _, [], _, _, _ => Nat.zero_le _
  | k, [], u :: l, r, h, _ => by simp at h
  | k, w :: ws, u :: l, r, h, hfit => by
    obtain ⟨rfl, rfl⟩ : u = w ∧ ws = l ++ r := by simpa [eq_comm] using h
    have hw : k + 1 + u.length ≤ M := by
      simp only [tailWidth, List.map_cons, List.sum_cons] at hfit
      omega
    have hl : k + 1 + u.length + tailWidth l ≤ M := by
      simp only [tailWidth, List.map_cons, List.sum_cons] at hfit ⊢
      omega
    unfold takeLine
    rw [if_pos hw]
    simpa using length_le_takeLine M _ (l ++ r) l r rfl hl

/-! ## The greedy fill is a layout -/

private lemma flatten_fillAux (M : ℕ) :
    ∀ (n : ℕ) (ws : List Word), ws.length ≤ n → (fillAux M n ws).flatten = ws
  | 0, ws, h => by rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 h)]; rfl
  | _ + 1, [], _ => rfl
  | n + 1, w :: ws, h => by
    have hr := takeLine_append M w.length ws
    have hlen : (takeLine M w.length ws).2.length ≤ n := by
      have := congrArg List.length hr
      simp only [List.length_append, List.length_cons] at this h
      omega
    simp only [fillAux, List.flatten_cons, flatten_fillAux M n _ hlen, List.cons_append, hr]

private lemma lines_fillAux (M : ℕ) :
    ∀ (n : ℕ) (ws : List Word), (∀ w ∈ ws, w.length ≤ M) →
      ∀ l ∈ fillAux M n ws, l ≠ [] ∧ (renderLine l).length ≤ M
  | 0, _, _ => by simp [fillAux]
  | _ + 1, [], _ => by simp [fillAux]
  | n + 1, w :: ws, h => by
    intro l hl
    simp only [fillAux, List.mem_cons] at hl
    rcases hl with rfl | hl
    · refine ⟨List.cons_ne_nil _ _, ?_⟩
      rw [length_renderLine_cons]
      exact tailWidth_takeLine_le M _ ws (h w (List.mem_cons_self ..))
    · refine lines_fillAux M n _ (fun u hu => h u ?_) l hl
      have hr := takeLine_append M w.length ws
      exact List.mem_cons_of_mem _ (hr ▸ List.mem_append_right _ hu)

/-- **The greedy fill is a layout** when every word fits on a line. -/
lemma layout_fill {M : ℕ} {ws : List Word} (h : ∀ w ∈ ws, w.length ≤ M) :
    Layout M ws (fill M ws) :=
  ⟨flatten_fillAux M _ ws le_rfl, fun hm => (lines_fillAux M _ ws h [] hm).1 rfl,
    fun l hl => (lines_fillAux M _ ws h l hl).2⟩

/-! ## No layout has fewer lines -/

/-- Dropping the first word of a layout leaves a layout with no more lines. -/
private lemma exists_layout_of_cons {M : ℕ} {w : Word} {ws : List Word} {ls : List Line}
    (h : Layout M (w :: ws) ls) : ∃ ls', Layout M ws ls' ∧ ls'.length ≤ ls.length := by
  obtain ⟨hf, hne, hfit⟩ := h
  rcases ls with _ | ⟨_ | ⟨u, l⟩, rest⟩
  · simp at hf
  · exact absurd (List.mem_cons_self ..) hne
  · simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
    obtain ⟨rfl, hf⟩ := hf
    simp only [List.mem_cons, not_or] at hne
    rcases l with _ | ⟨v, l⟩
    · refine ⟨rest, ⟨by simpa using hf, hne.2, fun l hl => hfit l (List.mem_cons_of_mem _ hl)⟩,
        by simp⟩
    · refine ⟨(v :: l) :: rest, ⟨by simpa using hf, ?_, fun l' hl' => ?_⟩, by simp⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨by simp, hne.2⟩
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · have h₁ := hfit _ (List.mem_cons_self ..)
          rw [length_renderLine_cons] at h₁
          rw [length_renderLine_cons]
          simp only [tailWidth, List.map_cons, List.sum_cons] at h₁ ⊢
          omega
        · exact hfit l' (List.mem_cons_of_mem _ hl')

/-- **What is left after a longer first line has a layout with no more lines.**
Dropping words from the front of a layout never adds a line. -/
private lemma exists_layout_of_append {M : ℕ} :
    ∀ (p : List Word) {ws : List Word} {ls : List Line}, Layout M (p ++ ws) ls →
      ∃ ls', Layout M ws ls' ∧ ls'.length ≤ ls.length
  | [], _, ls, h => ⟨ls, h, le_rfl⟩
  | w :: p, _, _, h => by
    obtain ⟨ls₁, h₁, hle₁⟩ := exists_layout_of_cons h
    obtain ⟨ls₂, h₂, hle₂⟩ := exists_layout_of_append p h₁
    exact ⟨ls₂, h₂, hle₂.trans hle₁⟩

private lemma length_fillAux_le {M : ℕ} :
    ∀ (n : ℕ) (ws : List Word), ws.length ≤ n →
      ∀ ls, Layout M ws ls → (fillAux M n ws).length ≤ ls.length
  | 0, _, _, _, _ => by simp [fillAux]
  | _ + 1, [], _, _, _ => by simp [fillAux]
  | n + 1, w :: ws, hn, ls, hl => by
    obtain ⟨hf, hne, hfit⟩ := hl
    rcases ls with _ | ⟨_ | ⟨u, l⟩, rest⟩
    · simp at hf
    · exact absurd (List.mem_cons_self ..) hne
    · simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
      obtain ⟨rfl, hf⟩ := hf
      simp only [List.mem_cons, not_or] at hne
      -- the first line of `ls` is `u :: l`; the greedy one takes at least `l`
      have hfirst : u.length + tailWidth l ≤ M := by
        rw [← length_renderLine_cons]; exact hfit _ (List.mem_cons_self ..)
      have hge := length_le_takeLine M u.length ws l rest.flatten hf.symm hfirst
      have hr := takeLine_append M u.length ws
      -- so what the greedy fill leaves is a suffix of what `ls` leaves
      obtain ⟨p, hp⟩ : ∃ p, rest.flatten = p ++ (takeLine M u.length ws).2 := by
        have h2 : l ++ rest.flatten = (takeLine M u.length ws).1 ++ (takeLine M u.length ws).2 :=
          hf.trans hr.symm
        rcases List.append_eq_append_iff.1 h2 with ⟨as, h₁, h₂⟩ | ⟨bs, h₁, h₂⟩
        · exact ⟨as, h₂⟩
        · have : l.length = (takeLine M u.length ws).1.length + bs.length := by
            rw [h₁, List.length_append]
          obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
          exact ⟨[], by simpa using h₂.symm⟩
      have hrest : Layout M (p ++ (takeLine M u.length ws).2) rest :=
        ⟨hp, hne.2, fun l' hl' => hfit l' (List.mem_cons_of_mem _ hl')⟩
      obtain ⟨ls', hls', hle⟩ := exists_layout_of_append p hrest
      have hlen : (takeLine M u.length ws).2.length ≤ n := by
        have := congrArg List.length hr
        simp only [List.length_append, List.length_cons] at this hn
        omega
      have := length_fillAux_le n _ hlen ls' hls'
      simp only [fillAux, List.length_cons]
      omega

/-- **No layout has fewer lines than the greedy fill.** -/
lemma length_fill_le {M : ℕ} {ws : List Word} {ls : List Line} (h : Layout M ws ls) :
    (fill M ws).length ≤ ls.length :=
  length_fillAux_le _ ws le_rfl ls h

/-! ## The characterisation -/

/-- **Filling line by line is correct**: on every input that has an output, the
greedy layout of its words, printed, is one. -/
theorem byLayout_fill {M : ℕ} {i : Text} (h : ∃ o, ByLayout M i o) :
    ByLayout M i (render (fill M (words i))) :=
  ⟨fill M (words i), layout_fill ((feasibility M i).1 h), fun _ hl => length_fill_le hl, rfl⟩

/-- **The checker decides `ByLayout`.** -/
theorem check_eq_true_iff (M : ℕ) (i o : Text) : check M i o = true ↔ ByLayout M i o := by
  have toText : ∀ {o : Text}, ByLayout M i o → ByText M i o := fun h => byLayout_eq_byText M ▸ h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hacc, hle⟩
    -- an acceptable text exists, so an output does, and the greedy one is an output
    obtain ⟨o', ho'⟩ := minSet_nonempty (List.count newline) (X := {o' | Acceptable M i o'})
      ⟨o, hacc⟩
    have hg := toText (byLayout_fill ⟨o', byLayout_eq_byText M ▸ byText_iff_minSet.2 ho'⟩)
    rw [byLayout_eq_byText]
    exact ⟨hacc, fun o'' h'' => hle.trans (hg.fewestLines o'' h'')⟩
  · intro h
    have hg := toText (byLayout_fill ⟨o, h⟩)
    exact ⟨(toText h).toFields, (toText h).fewestLines _ hg.toFields⟩

end Native
