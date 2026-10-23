import Meyer.Paper.Facts

/-!
# Deciding the 1985 specification

`Meyer.Paper.Spec` states `goal` as Meyer does, as a pipeline of set-builder
relations: a longest subsequence with single breaks, any exchange of breaks for
one another, a bound on the longest run without a new line, and a minimisation.
None of it can be evaluated as it stands -- `SINGLE_BREAKS` ranges over every
subsequence of the input, and `max_line_length` is a supremum -- so before this
module the only way to show that an output is acceptable was a proof by hand.

This module gives a function `check M i o : Bool` and proves that it decides
`goal`, `check_eq_true_iff`.  It runs in time linear in the length of the texts
and reduces in the kernel, so the `Decidable` instance built from it lets
`decide` settle concrete cases of realistic size (`Meyer.Paper.Check.Examples`).

## How

Three facts, each a characterisation of one stage of the pipeline.

* **`COMPACTED` is known up to the choice of break characters.**  `compact a`
  cuts each run of breaks in `a` down to its first character; it is a member of
  `COMPACTED (a)` (`compact_mem_compacted`), and every member is `EQUIVALENT` to
  it (`mem_equivalent_compact`).  So `TRANSF (i)` is `TRIMMED (compact i)`,
  `transf_eq_trimmed`, and the subsequences never have to be enumerated.  The
  proof is an exchange argument of the same shape as `Meyer.Paper.Retention`'s,
  with the same second invariant for "a break has just been kept", and it shows
  more than retention does: not only the words of a compaction are fixed, but
  its length and the position of every break as well.
* **`max_line_length` is computable**: `maxLineLength_eq` equates it to
  `maxLineLengthFrom 0`, one pass that counts the characters since the last new
  line.
* **The fewest new lines are those of the greedy fill.**  `fill M b` goes
  through `b` and makes each break a blank if the word after it still fits on
  the current line, and a new line otherwise.  It is in `TRIMMED (b)` whenever
  anything is (`fill_mem_trimmed`), and has no more new lines than anything that
  is (`numberOfNewLines_fill_le`).  The proof is the usual "greedy stays ahead"
  argument: at each break the greedy fill has either fewer new lines than a
  competitor, or as many and a current line no longer.

`goal_iff` puts them together, and `check` is `goal_iff` read as a program.

Why not go through `Native.ByLayout`, which is decidable and is proved equal to
the 2022 relation?  Its decision procedure enumerates the cuts of the list of
words, `2 ^ (n - 1)` of them, which is out of reach at the size of Naur's own
example sentence; and relating the 1985 relation to it would mean a proof about
the separators at the two ends of the text, where the two relations part, on top
of the minimisation that has to be computed directly in either case.

## The fill is a word wrap

To decide `goal` one has to know the fewest new lines any acceptable output
has, and this module knows it by producing an output that has them.  So `fill`,
composed with `compact`, is a line-by-line word wrap, and `goal_fill` says it is
correct in Meyer's sense: on the domain of `goal` it produces an acceptable
output.  It is the local, line-by-line reading of Naur's "each line is filled as
far as possible", and the theorem says that the 1985 specification, which reads
that phrase globally, admits it.  It does not say the converse: other outputs
with as few lines, filled differently, are admitted too.

## Separators only

Meyer asks, as the 2022 book's `T7`, what an input consisting of separators
alone should produce.  For the 1985 specification `goal_of_forall_isBreak`
answers it on every alphabet: a single blank when `MAXPOS ≥ 1`, and a single new
line when `MAXPOS = 0`, since then a blank is itself a line too long.
-/

namespace Meyer.Paper

variable {α : Type*} [DecidableEq α] [Alphabet α]

/-! ## `EQUIVALENT` is an equivalence -/

omit [DecidableEq α] in
/-- Every text is equivalent to itself. -/
private lemma mem_equivalent_self (s : Text α) : s ∈ Equivalent s :=
  List.forall₂_same.2 fun _ _ => Or.inl rfl

omit [DecidableEq α] in
/-- Equivalence is transitive: two exchanges of breaks compose to one. -/
private lemma mem_equivalent_trans {s b c : Text α} (h₁ : s ∈ Equivalent b)
    (h₂ : b ∈ Equivalent c) : s ∈ Equivalent c := by
  induction h₁ generalizing c with
  | nil => exact h₂
  | @cons x y s b hxy _ ih =>
    cases h₂ with
    | cons hyz h₂ =>
      refine List.Forall₂.cons ?_ (ih h₂)
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨-, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩

omit [DecidableEq α] in
/-- Consing a character onto both sides. -/
private lemma cons_mem_equivalent_cons {s b : Text α} (c : α) (h : s ∈ Equivalent b) :
    c :: s ∈ Equivalent (c :: b) :=
  List.Forall₂.cons (Or.inl rfl) h

/-! ## `COMPACTED`, computed

`compactFrom p a` keeps every letter of `a` and the first break of each run of
breaks; `p` records whether the character kept just before `a` was a break, in
which case a break at the front of `a` continues that run and is dropped too. -/

/-- Cut each run of breaks down to its first character.  The flag says whether
the last character kept was a break. -/
def compactFrom : Bool → Text α → Text α
  | _, [] => []
  | true, c :: t => if IsBreak c then compactFrom true t else c :: compactFrom false t
  | false, c :: t => if IsBreak c then c :: compactFrom true t else c :: compactFrom false t

/-- `compact a`: `a` with each run of breaks cut down to its first character.
It is a member of `COMPACTED (a)` (`compact_mem_compacted`), and up to the choice
of break characters the only one (`mem_equivalent_compact`). -/
def compact (a : Text α) : Text α :=
  compactFrom false a

/-- The text does not begin with a break; vacuously true of `[]`.  This is the
constraint a break just kept imposes on what follows. -/
private def NoBreakHead : Text α → Prop
  | [] => True
  | c :: _ => ¬ IsBreak c

omit [DecidableEq α] in
/-- `NoDoubleBreak` at a cons, as a statement about the head. -/
private lemma noDoubleBreak_cons_iff {c : α} {b : Text α} :
    NoDoubleBreak (c :: b) ↔ (IsBreak c → NoBreakHead b) ∧ NoDoubleBreak b := by
  cases b with
  | nil => simp [NoDoubleBreak, NoBreakHead]
  | cons d l => simp [NoDoubleBreak, NoBreakHead, List.isChain_cons_cons]

/-- `compactFrom` keeps characters of its argument, in order. -/
private lemma compactFrom_sublist : ∀ (p : Bool) (a : Text α), (compactFrom p a).Sublist a
  | _, [] => List.Sublist.slnil
  | true, c :: t => by
    unfold compactFrom
    split_ifs
    · exact (compactFrom_sublist true t).cons c
    · exact (compactFrom_sublist false t).cons_cons c
  | false, c :: t => by
    unfold compactFrom
    split_ifs
    · exact (compactFrom_sublist true t).cons_cons c
    · exact (compactFrom_sublist false t).cons_cons c

/-- `compactFrom` leaves single breaks, and does not begin with a break when
one has just been kept. -/
private lemma noDoubleBreak_compactFrom : ∀ (p : Bool) (a : Text α),
    NoDoubleBreak (compactFrom p a) ∧ (p = true → NoBreakHead (compactFrom p a))
  | _, [] => ⟨List.isChain_nil, fun _ => trivial⟩
  | true, c :: t => by
    unfold compactFrom
    split_ifs with hc
    · exact noDoubleBreak_compactFrom true t
    · exact ⟨noDoubleBreak_cons_iff.2 ⟨fun h => absurd h hc,
        (noDoubleBreak_compactFrom false t).1⟩, fun _ => hc⟩
  | false, c :: t => by
    unfold compactFrom
    split_ifs with hc
    · exact ⟨noDoubleBreak_cons_iff.2 ⟨fun _ => (noDoubleBreak_compactFrom true t).2 rfl,
        (noDoubleBreak_compactFrom true t).1⟩, nofun⟩
    · exact ⟨noDoubleBreak_cons_iff.2 ⟨fun h => absurd h hc,
        (noDoubleBreak_compactFrom false t).1⟩, nofun⟩

/-- Dropping the run at the front of `t` costs at most its one character, and
costs it exactly when `t` begins with a break, in which case the two compactions
differ by that break alone. -/
private lemma length_compactFrom_false {x : α} (hx : IsBreak x) (t : Text α) :
    (compactFrom false t).length ≤ (compactFrom true t).length + 1 ∧
      ((compactFrom false t).length = (compactFrom true t).length + 1 →
        compactFrom false t ∈ Equivalent (x :: compactFrom true t)) := by
  cases t with
  | nil => simp [compactFrom]
  | cons d t =>
    by_cases hd : IsBreak d
    · simp only [compactFrom, if_pos hd, List.length_cons, le_refl, true_and]
      exact fun _ => List.Forall₂.cons (Or.inr ⟨hd, hx⟩) (mem_equivalent_self _)
    · simp [compactFrom, if_neg hd]

/-- **Meyer's exchange argument, made exact.**  A subsequence of `a` with single
breaks -- one that does not begin with a break, if one has just been kept -- is
no longer than `compactFrom p a`, and if it is as long, it is `compactFrom p a`
with some of its breaks exchanged.

The induction runs on the derivation of the subsequence, and asks at each step
what happened to the first character of `a`.  The one case that needs care is a
dropped break with no break just kept: the competitor may keep a later break of
the same run instead, and `length_compactFrom_false` says it gains nothing by
it. -/
private lemma length_le_compactFrom {a y : Text α} (h : y.Sublist a) :
    ∀ p : Bool, NoDoubleBreak y → (p = true → NoBreakHead y) →
      y.length ≤ (compactFrom p a).length ∧
        (y.length = (compactFrom p a).length → y ∈ Equivalent (compactFrom p a)) := by
  induction h with
  | slnil => intro _ _ _; exact ⟨le_rfl, fun _ => List.Forall₂.nil⟩
  | @cons y t c h ih =>
    -- `c` was dropped.
    intro p hnd hbh
    by_cases hc : IsBreak c
    · cases p with
      | true =>
        simp only [compactFrom, if_pos hc]
        exact ih true hnd hbh
      | false =>
        simp only [compactFrom, if_pos hc, List.length_cons]
        obtain ⟨hle, heq⟩ := ih false hnd nofun
        obtain ⟨hle', heq'⟩ := length_compactFrom_false hc t
        refine ⟨hle.trans hle', fun hy => ?_⟩
        have hy' : y.length = (compactFrom false t).length := by omega
        exact mem_equivalent_trans (heq hy') (heq' (by omega))
    · have hlen : (compactFrom p (c :: t)).length = (compactFrom false t).length + 1 := by
        cases p <;> simp [compactFrom, if_neg hc]
      obtain ⟨hle, -⟩ := ih false hnd nofun
      rw [hlen]
      exact ⟨by omega, fun hy => by omega⟩
  | @cons_cons y t c h ih =>
    -- `c` was kept.
    intro p hnd hbh
    obtain ⟨hhead, hnd'⟩ := noDoubleBreak_cons_iff.1 hnd
    by_cases hc : IsBreak c
    · cases p with
      | true => exact absurd hc (hbh rfl)
      | false =>
        simp only [compactFrom, if_pos hc, List.length_cons]
        obtain ⟨hle, heq⟩ := ih true hnd' fun _ => hhead hc
        exact ⟨by omega, fun hy => cons_mem_equivalent_cons c (heq (by omega))⟩
    · have hcf : compactFrom p (c :: t) = c :: compactFrom false t := by
        cases p <;> simp [compactFrom, if_neg hc]
      rw [hcf]
      obtain ⟨hle, heq⟩ := ih false hnd' nofun
      simp only [List.length_cons]
      exact ⟨by omega, fun hy => cons_mem_equivalent_cons c (heq (by omega))⟩

/-- `compact a` is a member of `COMPACTED (a)`. -/
lemma compact_mem_compacted (a : Text α) : compact a ∈ Compacted a :=
  ⟨⟨compactFrom_sublist false a, (noDoubleBreak_compactFrom false a).1⟩,
    fun _ hy => (length_le_compactFrom hy.1 false hy.2 nofun).1⟩

/-- Every member of `COMPACTED (a)` is `compact a` with some breaks exchanged: a
compaction is determined up to which break character each run keeps. -/
lemma mem_equivalent_compact {a b : Text α} (hb : b ∈ Compacted a) :
    b ∈ Equivalent (compact a) := by
  obtain ⟨hle, heq⟩ := length_le_compactFrom hb.1.1 false hb.1.2 nofun
  exact heq (le_antisymm hle (hb.2 _ (compact_mem_compacted a).1))

/-- **`TRANSF (i)` is `TRIMMED (compact i)`.**  Since `EQUIVALENT` absorbs the
choice of break characters, the compaction contributes nothing to `TRANSF`
beyond `compact i`. -/
theorem transf_eq_trimmed (MAXPOS : ℕ) (i : Text α) :
    Transf MAXPOS i = Trimmed MAXPOS (compact i) := by
  ext s
  constructor
  · rintro ⟨b, hb, hs, hmax⟩
    exact ⟨mem_equivalent_trans hs (mem_equivalent_compact hb), hmax⟩
  · rintro ⟨hs, hmax⟩
    exact ⟨compact i, compact_mem_compacted i, hs, hmax⟩

/-! ## `max_line_length`, computed -/

/-- The longest line of `s` when its first line already holds `k` characters:
one pass, counting the characters since the last new line. -/
def maxLineLengthFrom : ℕ → Text α → ℕ
  | k, [] => k
  | k, c :: t => if c = newline then max k (maxLineLengthFrom 0 t) else maxLineLengthFrom (k + 1) t

omit [DecidableEq α] in
/-- A text without a new line is one line, as long as the text. -/
private lemma maxLineLength_of_newline_not_mem {p : Text α} (hp : newline ∉ p) :
    maxLineLength p = p.length :=
  le_antisymm (maxRun_le fun _ ht _ => ht.length_le) (length_le_maxLineLength_of_no_newline hp)

omit [DecidableEq α] in
/-- A new line splits the lines: the longest is the longer of those on either
side. -/
private lemma maxLineLength_append_newline (p t : Text α) :
    maxLineLength (p ++ newline :: t) = max (maxLineLength p) (maxLineLength t) := by
  unfold maxLineLength
  rw [show p ++ newline :: t = p ++ [newline] ++ t by simp]
  exact maxRun_append_mid (List.cons_ne_nil _ _) (by simp)

/-- `maxLineLengthFrom` is `max_line_length` with a newline-free text in front. -/
private lemma maxLineLengthFrom_length {p : Text α} (hp : newline ∉ p) (s : Text α) :
    maxLineLengthFrom p.length s = maxLineLength (p ++ s) := by
  induction s generalizing p with
  | nil => rw [List.append_nil, maxLineLength_of_newline_not_mem hp]; rfl
  | cons c t ih =>
    by_cases hc : c = newline
    · subst hc
      have h0 := ih (p := []) (List.not_mem_nil)
      rw [List.length_nil, List.nil_append] at h0
      rw [maxLineLengthFrom, if_pos rfl, h0, maxLineLength_append_newline,
        maxLineLength_of_newline_not_mem hp]
    · have hp' : newline ∉ p ++ [c] := by simp [hp, Ne.symm hc]
      rw [maxLineLengthFrom, if_neg hc, show p.length + 1 = (p ++ [c]).length by simp, ih hp',
        List.append_assoc, List.singleton_append]

/-- **`max_line_length` is computable.** -/
lemma maxLineLength_eq (s : Text α) : maxLineLength s = maxLineLengthFrom 0 s := by
  simpa using (maxLineLengthFrom_length (p := []) List.not_mem_nil s).symm

/-- A line is at least as long as what it already holds. -/
private lemma le_maxLineLengthFrom : ∀ (k : ℕ) (s : Text α), k ≤ maxLineLengthFrom k s
  | _, [] => le_rfl
  | k, c :: t => by
    unfold maxLineLengthFrom
    split_ifs
    · exact le_max_left _ _
    · exact (Nat.le_succ k).trans (le_maxLineLengthFrom (k + 1) t)

/-! ## The greedy fill -/

/-- The word at the front of a text: its characters up to the first break. -/
def firstWord : Text α → Text α
  | [] => []
  | c :: t => if IsBreak c then [] else c :: firstWord t

omit [DecidableEq α] in
/-- A letter is not a new line: `new_line` is a break. -/
private lemma ne_newline_of_not_isBreak {c : α} (hc : ¬ IsBreak c) : c ≠ newline :=
  fun h => hc (Or.inr h)

/-- The first word is a prefix. -/
private lemma firstWord_prefix : ∀ s : Text α, (firstWord s).IsPrefix s
  | [] => List.prefix_rfl
  | c :: t => by
    unfold firstWord
    split_ifs
    · exact List.nil_prefix
    · exact List.cons_prefix_cons.2 ⟨rfl, firstWord_prefix t⟩

/-- The first word has no break in it. -/
private lemma breakFree_firstWord : ∀ s : Text α, BreakFree (firstWord s)
  | [] => fun _ h => absurd h List.not_mem_nil
  | c :: t => by
    unfold firstWord
    split_ifs with hc
    · exact fun _ h => absurd h List.not_mem_nil
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc
      · exact breakFree_firstWord t x hx

/-- Exchanging breaks does not change the first word. -/
private lemma firstWord_eq_of_mem_equivalent {s t : Text α} (h : s ∈ Equivalent t) :
    firstWord s = firstWord t := by
  induction h with
  | nil => rfl
  | @cons x y s t hxy _ ih =>
    rcases hxy with rfl | ⟨hx, hy⟩
    · simp only [firstWord, ih]
    · simp [firstWord, hx, hy]

/-- The first line holds at least the first word. -/
private lemma add_length_firstWord_le : ∀ (k : ℕ) (s : Text α),
    k + (firstWord s).length ≤ maxLineLengthFrom k s
  | k, [] => by simp [firstWord, maxLineLengthFrom]
  | k, c :: t => by
    by_cases hc : IsBreak c
    · simpa [firstWord, hc] using le_maxLineLengthFrom k (c :: t)
    · have := add_length_firstWord_le (k + 1) t
      simp only [firstWord, if_neg hc, maxLineLengthFrom, if_neg (ne_newline_of_not_isBreak hc),
        List.length_cons]
      omega

variable (MAXPOS : ℕ)

/-- Fill line by line, the current line already holding `k` characters: each
break becomes a blank if the word after it still fits on the current line, and
a new line otherwise.  Every other character is kept. -/
def fillFrom : ℕ → Text α → Text α
  | _, [] => []
  | k, c :: t =>
    if IsBreak c then
      if k + 1 + (firstWord t).length ≤ MAXPOS then blank :: fillFrom (k + 1) t
      else newline :: fillFrom 0 t
    else c :: fillFrom (k + 1) t

/-- `fill MAXPOS b`: `b` filled line by line, greedily. -/
def fill (b : Text α) : Text α :=
  fillFrom MAXPOS 0 b

/-- **The checker.**  `o` is an acceptable output for `i` exactly when it is the
compacted input with breaks exchanged, its lines fit, and it has no more new
lines than the greedy fill of the compacted input.  `check_eq_true_iff`. -/
def check (i o : Text α) : Bool :=
  let b := compact i
  decide (o ∈ Equivalent b) && decide (maxLineLengthFrom 0 o ≤ MAXPOS) &&
    decide (numberOfNewLines o ≤ numberOfNewLines (fill MAXPOS b))

variable {MAXPOS}

/-- The fill only exchanges breaks. -/
private lemma fillFrom_mem_equivalent : ∀ (k : ℕ) (b : Text α), fillFrom MAXPOS k b ∈ Equivalent b
  | _, [] => List.Forall₂.nil
  | k, c :: t => by
    unfold fillFrom
    split_ifs with hc
    · exact List.Forall₂.cons (Or.inr ⟨Or.inl rfl, hc⟩) (fillFrom_mem_equivalent _ t)
    · exact List.Forall₂.cons (Or.inr ⟨Or.inr rfl, hc⟩) (fillFrom_mem_equivalent _ t)
    · exact cons_mem_equivalent_cons c (fillFrom_mem_equivalent _ t)

/-! ### The greedy fill has fewest new lines

Both halves need `blank ≠ newline`; on an alphabet where the two coincide there
is nothing to choose, and `EQUIVALENT (b)` is `{b}`. -/

omit [DecidableEq α] in
/-- Where the two separators coincide, a break can only be exchanged for
itself. -/
private lemma eq_of_mem_equivalent (hbn : (blank : α) = newline) {s b : Text α}
    (h : s ∈ Equivalent b) : s = b := by
  have key : ∀ x : α, IsBreak x → x = blank := fun x hx => hx.elim id (·.trans hbn.symm)
  induction h with
  | nil => rfl
  | @cons x y s b hxy _ ih =>
    rw [ih]
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · rw [key x hx, key y hy]

/-- Where the two separators coincide, the fill changes nothing. -/
private lemma fillFrom_eq_self (hbn : (blank : α) = newline) :
    ∀ (k : ℕ) (b : Text α), fillFrom MAXPOS k b = b :=
  fun k b => (eq_of_mem_equivalent hbn (fillFrom_mem_equivalent k b))

/-- **Greedy stays ahead.**  Compare the greedy fill, its current line holding
`kg` characters, with any `s` equivalent to `b` that fits, its current line
holding `ks`.  If the greedy line is no longer, the greedy fill has no more new
lines; and in any case it has at most one more.

Where the two make the same choice at a break, both halves carry over.  Where
`s` puts a new line and the greedy fill a blank, the greedy fill has saved a new
line, and the second half, from there on, gives the first.  Where `s` puts a
blank and the greedy fill a new line, the word after the break fitted on the
line of `s` and not on the greedy one, so the greedy line was the longer and
only the second half is claimed; the first half, from the empty line that
follows, gives it. -/
private lemma count_fillFrom_le (hbn : (blank : α) ≠ newline) {s b : Text α}
    (h : s ∈ Equivalent b) : ∀ kg ks : ℕ, maxLineLengthFrom ks s ≤ MAXPOS →
      (kg ≤ ks → numberOfNewLines (fillFrom MAXPOS kg b) ≤ numberOfNewLines s) ∧
        numberOfNewLines (fillFrom MAXPOS kg b) ≤ numberOfNewLines s + 1 := by
  induction h with
  | nil => intro _ _ _; simp [fillFrom, numberOfNewLines]
  | @cons y x s' t hyx hrest ih =>
    intro kg ks hfit
    by_cases hx : IsBreak x
    · have hy : IsBreak y := hyx.elim (· ▸ hx) And.left
      have hw : firstWord s' = firstWord t := firstWord_eq_of_mem_equivalent hrest
      rcases hy with rfl | rfl
      · -- `s` keeps a blank
        have hfit' : maxLineLengthFrom (ks + 1) s' ≤ MAXPOS := by
          simpa [maxLineLengthFrom, hbn] using hfit
        have hword := (add_length_firstWord_le (ks + 1) s').trans hfit'
        rw [hw] at hword
        have hcnt : numberOfNewLines (blank :: s') = numberOfNewLines s' := by
          simp [numberOfNewLines, hbn]
        rw [hcnt]
        unfold fillFrom
        rw [if_pos hx]
        split_ifs with hg
        · have hb : numberOfNewLines (blank :: fillFrom MAXPOS (kg + 1) t) =
              numberOfNewLines (fillFrom MAXPOS (kg + 1) t) := by
            simp [numberOfNewLines, hbn]
          rw [hb]
          obtain ⟨h₁, h₂⟩ := ih (kg + 1) (ks + 1) hfit'
          exact ⟨fun hk => h₁ (by omega), h₂⟩
        · have hb : numberOfNewLines (newline :: fillFrom MAXPOS 0 t) =
              numberOfNewLines (fillFrom MAXPOS 0 t) + 1 := by
            simp [numberOfNewLines]
          rw [hb]
          exact ⟨fun hk => absurd (by omega) hg, by
            have := (ih 0 (ks + 1) hfit').1 (Nat.zero_le _); omega⟩
      · -- `s` keeps a new line
        have hfit' : maxLineLengthFrom 0 s' ≤ MAXPOS := by
          simp only [maxLineLengthFrom] at hfit
          exact (le_max_right _ _).trans hfit
        have hcnt : numberOfNewLines (newline :: s') = numberOfNewLines s' + 1 := by
          simp [numberOfNewLines]
        rw [hcnt]
        unfold fillFrom
        rw [if_pos hx]
        split_ifs with hg
        · have hb : numberOfNewLines (blank :: fillFrom MAXPOS (kg + 1) t) =
              numberOfNewLines (fillFrom MAXPOS (kg + 1) t) := by
            simp [numberOfNewLines, hbn]
          rw [hb]
          have := (ih (kg + 1) 0 hfit').2
          exact ⟨fun _ => this, by omega⟩
        · have hb : numberOfNewLines (newline :: fillFrom MAXPOS 0 t) =
              numberOfNewLines (fillFrom MAXPOS 0 t) + 1 := by
            simp [numberOfNewLines]
          rw [hb]
          have := (ih 0 0 hfit').1 le_rfl
          exact ⟨fun _ => by omega, by omega⟩
    · -- a letter, the same in both
      obtain rfl : y = x := hyx.resolve_right fun h => hx h.2
      have hn := ne_newline_of_not_isBreak hx
      have hfit' : maxLineLengthFrom (ks + 1) s' ≤ MAXPOS := by
        simpa [maxLineLengthFrom, hn] using hfit
      have hcnt : ∀ u : Text α, numberOfNewLines (y :: u) = numberOfNewLines u := fun u => by
        simp [numberOfNewLines, hn]
      unfold fillFrom
      rw [if_neg hx, hcnt, hcnt]
      obtain ⟨h₁, h₂⟩ := ih (kg + 1) (ks + 1) hfit'
      exact ⟨fun hk => h₁ (by omega), h₂⟩

/-- **The greedy fill fits**, provided every word of `b` fits on a line and the
first fits on the current one. -/
private lemma maxLineLengthFrom_fillFrom_le (hbn : (blank : α) ≠ newline) :
    ∀ (k : ℕ) (b : Text α), k + (firstWord b).length ≤ MAXPOS →
      (∀ u, u.IsSuffix b → (firstWord u).length ≤ MAXPOS) →
        maxLineLengthFrom k (fillFrom MAXPOS k b) ≤ MAXPOS
  | k, [], hk, _ => by simpa [fillFrom, maxLineLengthFrom] using hk
  | k, c :: t, hk, hw => by
    have hw' : ∀ u, u.IsSuffix t → (firstWord u).length ≤ MAXPOS :=
      fun u hu => hw u (hu.trans (List.suffix_cons c t))
    unfold fillFrom
    by_cases hc : IsBreak c
    · rw [if_pos hc]
      split_ifs with hg
      · simp only [maxLineLengthFrom, if_neg hbn]
        exact maxLineLengthFrom_fillFrom_le hbn (k + 1) t hg hw'
      · simp only [maxLineLengthFrom]
        simp only [firstWord, if_pos hc, List.length_nil, add_zero] at hk
        exact max_le hk (maxLineLengthFrom_fillFrom_le hbn 0 t
          (by simpa using hw' t List.suffix_rfl) hw')
    · rw [if_neg hc]
      simp only [maxLineLengthFrom, if_neg (ne_newline_of_not_isBreak hc)]
      simp only [firstWord, if_neg hc, List.length_cons] at hk
      exact maxLineLengthFrom_fillFrom_le hbn (k + 1) t (by omega) hw'

/-- Anything in `TRIMMED (b)` bounds the words of `b`, and so each first word
of a suffix of `b`, by `MAXPOS`. -/
private lemma length_firstWord_le {b s : Text α} (hs : s ∈ Trimmed MAXPOS b) {u : Text α}
    (hu : u.IsSuffix b) : (firstWord u).length ≤ MAXPOS :=
  (mem_noOversizeWord_iff MAXPOS b).1 (mem_noOversizeWord_of_mem_trimmed hs) _
    ((firstWord_prefix u).isInfix.trans hu.isInfix) (breakFree_firstWord u)

/-- **The greedy fill is in `TRIMMED (b)`** whenever anything is. -/
lemma fill_mem_trimmed {b : Text α} (h : (Trimmed MAXPOS b).Nonempty) :
    fill MAXPOS b ∈ Trimmed MAXPOS b := by
  by_cases hbn : (blank : α) = newline
  · obtain ⟨s, hs⟩ := h
    obtain rfl := eq_of_mem_equivalent hbn hs.1
    rw [fill, fillFrom_eq_self hbn]
    exact hs
  · obtain ⟨s, hs⟩ := h
    refine ⟨fillFrom_mem_equivalent 0 b, ?_⟩
    rw [maxLineLength_eq]
    exact maxLineLengthFrom_fillFrom_le hbn 0 b
      (by simpa using length_firstWord_le hs List.suffix_rfl)
      fun u hu => length_firstWord_le hs hu

/-- **The greedy fill has no more new lines than anything in `TRIMMED (b)`.** -/
lemma numberOfNewLines_fill_le {b s : Text α} (hs : s ∈ Trimmed MAXPOS b) :
    numberOfNewLines (fill MAXPOS b) ≤ numberOfNewLines s := by
  by_cases hbn : (blank : α) = newline
  · rw [fill, fillFrom_eq_self hbn, eq_of_mem_equivalent hbn hs.1]
  · exact (count_fillFrom_le hbn hs.1 0 0 (by rw [← maxLineLength_eq]; exact hs.2)).1 le_rfl

/-! ## The characterisation -/

/-- **`goal`, characterised.**  An acceptable output is the compacted input with
breaks exchanged, with no line longer than `MAXPOS`, and with no more new lines
than the greedy fill. -/
theorem goal_iff (i o : Text α) :
    Goal MAXPOS i o ↔ o ∈ Trimmed MAXPOS (compact i) ∧
      numberOfNewLines o ≤ numberOfNewLines (fill MAXPOS (compact i)) := by
  rw [Goal, FewestLines, MinSet, transf_eq_trimmed]
  exact ⟨fun ⟨ho, hmin⟩ => ⟨ho, hmin _ (fill_mem_trimmed ⟨o, ho⟩)⟩,
    fun ⟨ho, hle⟩ => ⟨ho, fun _ hy => hle.trans (numberOfNewLines_fill_le hy)⟩⟩

/-- **The checker decides `goal`.** -/
theorem check_eq_true_iff (i o : Text α) : check MAXPOS i o = true ↔ Goal MAXPOS i o := by
  rw [goal_iff, Trimmed, Set.mem_setOf_eq, maxLineLength_eq]
  simp [check, and_assoc]

/-- `goal` is decidable, by `check`.  The instance reduces in the kernel, so
`decide` settles concrete instances. -/
instance (i o : Text α) : Decidable (Goal MAXPOS i o) :=
  decidable_of_iff _ (check_eq_true_iff i o)

/-- **Filling line by line is correct.**  On the domain of `goal`, the greedy
fill of the compacted input is an acceptable output, so the word wrap
`fill MAXPOS ∘ compact`, restricted to that domain, is correct in the sense of
`IsCorrect`. -/
theorem goal_fill {i : Text α} (hi : i ∈ DomGoal α MAXPOS) :
    Goal MAXPOS i (fill MAXPOS (compact i)) := by
  obtain ⟨o, ho⟩ := hi
  rw [goal_iff] at ho ⊢
  exact ⟨fill_mem_trimmed ⟨o, ho.1⟩, le_rfl⟩

/-! ## An input of separators only -/

/-- A run of breaks after a kept break is dropped entirely. -/
private lemma compactFrom_true_of_forall_isBreak :
    ∀ {t : Text α}, (∀ c ∈ t, IsBreak c) → compactFrom true t = []
  | [], _ => rfl
  | c :: t, h => by
    rw [compactFrom, if_pos (h c (List.mem_cons_self ..))]
    exact compactFrom_true_of_forall_isBreak fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **The 1985 answer to `T7`.**  An input made of separators only, and not empty,
has exactly one output: a single blank if `MAXPOS ≥ 1`, and a single new line if
`MAXPOS = 0`, where the blank would make a line one character too long.  The 2022
specification gives the empty text, `Meyer.Book.solutions_of_forall_isSeparator`.

On an alphabet where `blank` and `new_line` coincide the two cases are one, and
the statement still holds. -/
theorem goal_of_forall_isBreak {i : Text α} (hne : i ≠ []) (h : ∀ c ∈ i, IsBreak c)
    (o : Text α) : Goal MAXPOS i o ↔ o = if 1 ≤ MAXPOS then [blank] else [newline] := by
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc : IsBreak c := h c (List.mem_cons_self ..)
  have hcomp : compact (c :: t) = [c] := by
    rw [compact, compactFrom, if_pos hc,
      compactFrom_true_of_forall_isBreak fun x hx => h x (List.mem_cons_of_mem _ hx)]
  have hfill : fill MAXPOS [c] = if 1 ≤ MAXPOS then [blank] else [newline] := by
    simp [fill, fillFrom, firstWord, hc]
  have hequiv : ∀ y : α, IsBreak y → [y] ∈ Equivalent [c] :=
    fun y hy => List.Forall₂.cons (Or.inr ⟨hy, hc⟩) List.Forall₂.nil
  rw [goal_iff, hcomp, hfill, Trimmed, Set.mem_setOf_eq, maxLineLength_eq]
  constructor
  · rintro ⟨⟨ho, hfit⟩, hcnt⟩
    obtain ⟨y, hyc, rfl⟩ : ∃ y, (y = c ∨ (IsBreak y ∧ IsBreak c)) ∧ o = [y] := by
      rcases ho with _ | ⟨hyc, hrest⟩
      exact ⟨_, hyc, by rw [List.forall₂_nil_right_iff.1 hrest]⟩
    have hy : IsBreak y := hyc.elim (· ▸ hc) And.left
    by_cases hbn : (blank : α) = newline
    · rcases hy with rfl | rfl <;> simp [hbn]
    · split_ifs with hM
      · rcases hy with rfl | rfl
        · rfl
        · simp [numberOfNewLines, hM, Ne.symm hbn] at hcnt
      · rcases hy with rfl | rfl
        · simp [maxLineLengthFrom, hbn] at hfit
          omega
        · rfl
  · rintro rfl
    split_ifs with hM
    · exact ⟨⟨hequiv _ (Or.inl rfl), by
        by_cases hbn : (blank : α) = newline <;> simp [maxLineLengthFrom, hbn, hM]⟩, le_rfl⟩
    · exact ⟨⟨hequiv _ (Or.inr rfl), by simp [maxLineLengthFrom]⟩, le_rfl⟩

end Meyer.Paper
