# formalism-lean

Bertrand Meyer wrote a formal specification of word wrap twice, thirty-seven years
apart. This repository transcribes both into Lean 4 and proves the results each text
states about its own specification: Meyer's two claims from 1985, and `T1` to `T8` from
the 2022 chapter. It then adds a third specification of the same problem, written to
use what Lean already has rather than to transcribe a text — given twice, by layouts
and on the output text, and the two proved the same relation — and proves it to be the
2022 relation exactly and the 1985 relation not at all.

> Bertrand Meyer, *On Formalism in Specifications*, IEEE Software 2(1):6–26, 1985.
> [DOI 10.1109/MS.1985.229776](https://doi.org/10.1109/MS.1985.229776) ·
> [free PDF](https://se.inf.ethz.ch/~meyer/publications/ieee/formalism.pdf)

> Bertrand Meyer, *Handbook of Requirements and Business Analysis*, Springer, 2022.
> Chapter 9, "Benefiting from formal methods", §9.5.
> [DOI 10.1007/978-3-031-06739-6](https://doi.org/10.1007/978-3-031-06739-6)

The problem has a long and interesting history:

- **Naur (1969)** poses it, gives a program, and gives a *proof* that the program
  satisfies it.
- **Goodenough & Gerhart (1975)** find seven errors in that proved program.
  Concluding the specification was at fault, they write a new one, four times
  longer, and revise it again in 1977.
- **Meyer (1985)** takes that carefully rewritten specification and exhibits six of
  his seven "sins of the specifier" in it, then gives a formal specification of his
  own, from which the error case follows as a theorem: the problem has no solution
  when the input contains a word longer than `MAXPOS`. Goodenough and Gerhart had
  stipulated that case rather than deriving it.
- **Meyer (2022)** returns to the example and specifies it again from scratch, with
  different machinery and eight stated properties.

Everything here is sorry-free and depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

As of August 2026, searches of the literature, arXiv, GitHub and the Lean community
archives turned up no earlier public mechanisation of either specification. That is a
report of what we looked for, not a systematic review.

## Modules

| Module | Contents |
|---|---|
| `Meyer.lean` | umbrella; `import Meyer` brings in everything |
| `Meyer/Common.lean` | what the two treatments share: the alphabet classes `Alphabet` (1985) and `Lettered` (2022) — the transcriptions never mention `Char` — texts, separators, `Spec` (a specification is a relation between input and output), `MAX_SET`/`MIN_SET`, and `maxRun`, the common generalisation of the paper's `max_line_length` and the book's `maxline`, `maxword` and `M6` |
| `Meyer/Paper/Spec.lean` | the 1985 specification: `SINGLE_BREAKS`, `COMPACTED`, `EQUIVALENT`, `TRIMMED`, `FEWEST_LINES`, `goal`. Definitions only |
| `Meyer/Paper/Lemmas.lean` | basic API, and Meyer's condition for `TRIMMED (b)` to be nonempty |
| `Meyer/Paper/Retention.lean` | the step Meyer asserts without proof: compacting a text does not change its words |
| `Meyer/Paper/Facts.lean` | Meyer's two claims, proved |
| `Meyer/Paper/Bug.lean` | a defect in the paper, proved |
| `Meyer/Paper/Examples.lean` | `WHO WHAT WHEN` at `Char`; the letterless alphabet `Bool` |
| `Meyer/Book/Spec.lean` | the 2022 specification: `recast1`, `recast`, `maxword`, `maxline`, the `mu` operator, `S1`. Definitions only |
| `Meyer/Book/Recast.lean` | properties of the recasting relation |
| `Meyer/Book/Words.lean` | words and breaks (exercise 9-E.6) |
| `Meyer/Book/Facts.lean` | the chapter's eight claims `T1` to `T8`, proved |
| `Meyer/Book/Bug.lean` | a defect in the book, proved |
| `Meyer/Book/Examples.lean` | `␣␣ABC␣␣D␣␣EFG` at `Char`, with its two solutions and the defect's third |
| `Meyer/Comparison.lean` | the two specifications are not the same relation |
| `Meyer/Comparison/Examples.lean` | `␣AB` at `Char`: the empty first line |
| `Meyer/Char.lean` | `Char` as an alphabet of both kinds |
| `Native.lean` | umbrella for the third specification |
| `Native/Spec.lean` | the Lean-native specification twice over: `ByLayout` and `ByText`. Definitions only |
| `Native/Properties.lean` | decidability, feasibility, nondeterminism, and `ByLayout M = ByText M` |
| `Native/Comparison.lean` | `ByLayout M = Meyer.Book.Goal M` |

## The 1985 paper

The headline results, both in `Meyer/Paper/Facts.lean`:

```lean
theorem goal_not_functional :
    ∃ (n : ℕ) (i o₁ o₂ : Text Char), Goal n i o₁ ∧ Goal n i o₂ ∧ o₁ ≠ o₂

theorem domGoal_eq_noOversizeWord : DomGoal α MAXPOS = NoOversizeWord α MAXPOS
```

The witness for the first is Meyer's own, `WHO WHAT WHEN` at `MAXPOS = 10`, which
`goal` relates to both two-line outputs. The second is assembled from the three
sentences of his derivation, one lemma per sentence.

### What formalising it turned up

**1. The definition of "subsequence" is wrong as written.** Meyer defines a
subsequence of `s` as `s ∘ u` for `u` a *sorted* sequence of positions, and defines
sorted with a non-strict `≤`. So a position may repeat: in his own example
`<a b a a b d c d>`, the index sequence `<3 3 3 3>` is sorted, making `<a a a a>` a
"subsequence", and a run of any length qualifies just as well.

`COMPACTED (a)` asks for the *longest* members of `SINGLE_BREAKS (a)`. Whenever `a` contains
a character that is not a break, repetition supplies members of every length, so there is no
longest and `a` has no output at all. Under the literal reading `dom (goal)` therefore holds
only texts made of break characters (`Meyer.Paper.Bug.domGoal_subset_breaksOnly`): the
specification cannot format any text with a letter in it, Meyer's own `WHO WHAT WHEN`
included (`Meyer/Paper/Examples.lean`). His domain theorem says `dom (goal)` is the set of
texts with no word longer than `MAXPOS`, so for any `MAXPOS ≥ 1` a one-letter text
contradicts it. The two cannot both stand, and since the theorem is what he proves, the
literal reading is the one that goes.

`Meyer/Paper/Bug.lean` proves that, and proves the literal reading is the more permissive
of the two: the defect adds members to `SINGLE_BREAKS` and removes none. Its docstring
carries the detail. Meyer had in fact written a guard against precisely this hazard,
noting that `MAX_SET` "is not always defined" and must be applied "only to sets `X` which
are finite"; the one-line argument he gives to discharge it is what the literal reading
falsifies.

Note which half is at fault. His description in the running text, "a sequence made of
zero or more of the elements of `s`, in the same order as in `s`", is correct; the
formal definition printed beside it is what admits repetition. In a paper arguing that
formalism repairs the imprecision of prose, the prose was right and the formalism was
wrong.

**2. The domain theorem rests on a lemma Meyer states only in passing.** The theorem
needs to know that compacting a text leaves its *words* intact. Meyer says so in a
parenthetical remark (omit a non-break character and it could be reinserted to give a
longer member of `SINGLE_BREAKS`) and never returns to it. The gap shows in his
derivation: he states the solvability condition for the *compacted* text, then states
the theorem about the *input*, without saying what carries one to the other.

The remark is sound in outline, but the induction it suggests fails and needs a second
invariant to go through; `Meyer/Paper/Retention.lean` gives the counterexample and the
repair. With retention in hand, `Meyer/Paper/Facts.lean` follows Meyer's derivation
sentence by sentence.

**3. Nothing else was wrong.** Under the corrected, strictly increasing reading of
"subsequence", both of Meyer's claims are true and the rest of the specification
transcribes without incident.

## The 2022 book

The chapter states eight properties of its specification and proves or sketches each.
All eight are true, and all are proved here:

| | claim | where |
|---|---|---|
| `T1` | `out.count ≤ in.count` | `Book.length_le_of_recast` |
| `T2` | `maxword (out) ≤ maxline (out)` | `Book.maxWord_le_maxLine` |
| `T3` | `WORDS (out) = WORDS (in)` | `Book.words_eq_of_recast` |
| `T4` | `breaks (out).count ≥ breaks (in).count − 2` | `Book.length_breaks_ge` |
| `T5` | there can be more than one solution | `Book.goal_not_functional` |
| `T6` | no solution starts or ends with a break | `Book.solution_not_isSeparator_at_ends` |
| `T7` | an all-separator input gives an empty output | `Book.solutions_of_forall_isSeparator` |
| `T8` | a solution exists iff `maxword (in) ≤ M` | `Book.feasibility` |

Also proved: the "minimization lemma" of §9.5.6 (exercise 9-E.5), the equivalence of
`M5` and `M6`, and, of exercise 9-E.6, definitions of `WORDS` and `breaks` together with
the properties `T3` and `T4` need. Its alternating-decomposition theorem is not stated.
`T5` is proved for any alphabet with a letter `c` and two distinct separators, on the
input `c cc c` at `M = 4`; Meyer's own witness, `␣␣ABC␣␣D␣␣EFG` at `M = 5`, is the `Char`
example beside it.

### What formalising it turned up

**1. `S1` admits unintended solutions.** `M3` says something other than what its
prose says. The measure the specification minimises last is

> `new_lines (out) ≜ |{x: range out | x = new_line}|`

where `|A|` is the cardinal of `A`. Meyer writes it with a bar over `A` and gives
`|A|` as the alternative notation (p. 162). But `range` is the set of *values* of a
sequence, and §9.2.6 is explicit that this collapses repetitions: "`[1, 2, 2]` and
`[1, 2]` have the same range, `{1, 2}`, but are different sequences." So the measure is
`0` or `1`, never the number of new lines. Meyer wanted an index set, which is what he
wrote in 1985: `card {i ∈ 1..length (s) | s (i) = new_line}`. That set ranges over
positions, so two new lines at different positions stay two elements, and the paper has
no counterpart to this defect.

Read literally, the measure only distinguishes "has a new line" from "has none", so
minimising it decides anything only when some candidate fits on a single line. Whenever
the text actually has to be wrapped, every candidate scores `1` and the requirement is
vacuous. The specification stops asking that lines be filled. For the input above,
`␣␣ABC␣␣D␣␣EFG` at `M = 5`, Meyer displays the two solutions `ABC␣D / EFG` and
`ABC / D␣EFG`. The literal reading admits a third, `ABC / D / EFG`, on three lines where
two suffice. `Meyer/Book/Bug.lean` proves this, and also proves the defect is the more
permissive reading: it accepts every output the intended reading accepts, and more.

No theorem in the chapter is falsified by it. `T1` to `T4` are about the recasting
relation and never reach the measure at all, and `T8`, the one substantial result, asks
only whether the set of solutions is nonempty, which minimising a different measure over
the same nonempty set preserves. Proving the chapter's properties, by hand or by
machine, would not have found the defect. Only the inclusion and the extra witness are
mechanised; the survey of all eight is an argument, not a theorem.

The 1985 defect is the opposite case: it makes Meyer's own domain theorem false, so
mechanising the paper catches it at once, and it survived only because the derivation
was three sentences of prose that silently used the intended meaning of
"subsequence".

**2. The proof sketch for `T8` applies the minimisation lemma to the wrong set.** The
theorem is correct as stated, and neither the specification nor any of the other seven
statements is affected. This is about the argument given for it on p. 177, and nothing
else.

`S1` minimises `out.count` before imposing the line limit, so the lemma needs a
*shortest* recast with short enough lines. Meyer shows that *a* recast has short enough
lines. His witness `owpl`, one word per line, happens to be a shortest recast as well,
so the conclusion holds, but the proof never says so and never mentions length. Saying
so needs `T3` and the bound that a text is at least as long as its letters plus one
separator per gap between words, which is exercise 9-E.6. Both are proved in
`Meyer/Book/Words.lean`; the gap is recorded in the module docstring of
`Meyer/Book/Facts.lean`.

**3. Nothing further was found in `S1` or in `T1` to `T8`.** All eight properties are
true and the specification otherwise transcribes without incident. Two defects lie
outside them and are recorded in the module docstrings rather than here: the termination
argument of p. 173, which `Meyer.Book.recast1_cycle` refutes by exhibiting a space and a
new line that rewrite to each other for ever, and the English restatement of §9.5.7,
whose clause 4 cannot exchange an isolated separator and so cannot produce most of the
outputs `S1` admits. Neither is formalised beyond that theorem, and the chapter's
remaining inconsistencies are editorial.

## How the two specifications differ

Meyer guessed that the two solutions were "probably similar in spirit". They are, and
they derive the same solvability condition. But they are not the same relation. They
part company over the separators at the two ends of the text.

The paper compacts by taking a *longest* subsequence with no two adjacent break
characters, so a leading break survives as one character. The book compacts by taking a
*shortest* recast, and its `[L]` and `[T]` delete leading and trailing breaks outright;
Meyer states the consequence himself as `T6`.

The difference is not only cosmetic. For the input `␣AB` with a line limit of two
characters, the paper cannot leave the blank where it is, because the line `␣AB` is
three characters long. It must turn the blank into a new line, so its output has an
empty first line. The book deletes the blank. `Meyer/Comparison/Examples.lean` checks
this at `Char` by `decide`. `Meyer/Comparison.lean` proves the divergence for every
alphabet on the smallest possible input: at line limit one the two disagree on the
one-character text `[space]`, which the paper keeps and the book deletes
(`specifications_differ`, each output rejected by the other; `paper_ne_book`, the two as
different elements of `Spec`); see [Alphabets](#alphabets).

The same divergence bears on a question Meyer raises as `T7` and leaves open for the
natural-language originals. For an input of separators only the book yields the empty
text, which is `Meyer.Book.solutions_of_forall_isSeparator`; the 1985 specification
yields a single space, provided `MAXPOS ≥ 1`. At `MAXPOS = 0` a space is itself a line
one character long, so the paper's output is a new line instead. Neither half of the
1985 answer is mechanised.

## A third specification, Lean-native

Both of Meyer's specifications keep the text as a sequence of characters and recover
its structure from that sequence: the paper by taking a longest subsequence with no two
adjacent break characters, the book by taking a shortest element of the closure of a
rewriting relation, and both by measuring a line as the longest run of characters
containing no new line. `Native/Spec.lean` writes the same problem the other way round,
and writes it twice: once by way of layouts, `ByLayout`, and once on the output text
alone, `ByText`. The two share a single definition, the words of the input, and
`Native/Properties.lean` proves them the same relation.

```lean
def words (t : Text) : List Word := (t.splitOnP (IsBreak ·)).filter (· ≠ [])
```

A `Word` is a `Text`, a `Line` is a `List Word`, and `words` is the book's `WORDS`
character for character. It is the only place either specification looks at a
character. Both specifications have the type `Spec Char`, where `Spec α := Text α → Text α → Prop`
in `Meyer/Common.lean` is a relation between input and output — which is what the 1985
paper says a specification is. The native specification is concrete over `Char`, an
alphabet of both of Meyer's kinds; his are abstract, see [Alphabets](#alphabets).

### By layouts

```lean
def renderLine (l : Line) : Text := List.intercalate [blank] l
def render (ls : List Line) : Text := List.intercalate [newline] (ls.map renderLine)

variable (M : ℕ)   -- the line limit, Naur's MAXPOS

structure Layout (ws : List Word) (ls : List Line) : Prop where
  flatten  : ls.flatten = ws
  nonempty : [] ∉ ls
  fits     : ∀ l ∈ ls, (renderLine l).length ≤ M

def ByLayout : Spec Char := fun i o =>
  ∃ ls, Layout M (words i) ls ∧
    (∀ ls', Layout M (words i) ls' → ls.length ≤ ls'.length) ∧ o = render ls
```

An output is the printed form of a layout of the words, one with as few lines as any.
What the change of representation buys, against Meyer's two:

- **No supremum over runs.** The line limit is a bounded quantifier over a list, and
  `maxRun`, with its nonemptiness and boundedness obligations, is not needed.
- **No finiteness side condition.** A layout of `n` words is one of the finitely many
  cuts of a list of length `n`, so the minimum exists without the care Meyer takes over
  `MAX_SET` in the paper's box "The reasoning behind formal specifications".
- **Decidability.** `Native/Properties.lean` proves `ByLayout` decidable, so the worked
  examples, Meyer's `␣␣ABC␣␣D␣␣EFG` at `M = 5` and `WHO WHAT WHEN` at `MAXPOS = 10`,
  are settled by `decide` rather than by hand. The specification is still a
  proposition; that it can be evaluated is a theorem about it.
- **Nothing to retain.** The words are the primitive, so the step the paper asserts in
  passing and `Meyer/Paper/Retention.lean` spends its effort on has no counterpart.

The properties Meyer proves sort into two kinds. `T2`, `T6`, `T7` and `T8` have short
counterparts (`Native.feasibility` is `T8` and the paper's domain theorem, on the words
directly). `T1`, `T3` and `T4` have no statement at all: they are properties of the
character encoding, not of the problem.

### On texts

```lean
structure Acceptable.Fields (i o : Text) : Prop where
  linesFit     : o ≠ [] → ∀ l ∈ o.splitOn newline, l ≠ [] ∧ l.length ≤ M   -- N1
  singleBlanks : o ≠ [] → ∀ l ∈ o.splitOn newline, [] ∉ l.splitOn blank     -- N2
  sameWords    : words o = words i                                           -- N3
abbrev Acceptable : Spec Char := Acceptable.Fields M

structure ByText.Fields (i o : Text) : Prop extends Acceptable.Fields M i o where
  fewestLines  : ∀ o', Acceptable M i o' → o.count newline ≤ o'.count newline  -- N4
abbrev ByText : Spec Char := ByText.Fields M
```

An output is an acceptable text with the fewest lines, where acceptable means: every
line is non-empty and fits, words are separated by single blanks with none at the ends,
and the words are the input's. (`N1` and `N2` carry the proviso `o ≠ []`, since
`List.splitOn` reads the empty text as one empty line.) `Acceptable` is the candidate
relation `ByText` minimises over; it has the type of a specification and is not one.
Nothing stands behind the four conditions — no layout, no `render` — and where
`ByLayout` constructs the output with `List.intercalate`, `ByText` inspects it with
`List.splitOn`.

This is Naur's problem statement, in the global reading of "filled as far as
possible", written on the output. It also has the shape both of Meyer's specifications
have, a minimisation over a set of candidates: `ByText M i` is `MIN_SET` of the
acceptable texts under the number of new lines (`Native.byText_iff_minSet`), as the
1985 `goal` is `MIN_SET` of `TRANSF (i)`. The difference is that the candidate set is
described by three checks on the text rather than constructed by a pipeline of
relations.

The four conditions are labelled `N1` to `N4` because they stand where the book's `T1`
to `T8` stand — each is something one would want to prove of an output — with one
difference of status: the book's are claims about `S1`, these are the specification.
`N1` and `N2` are the book's `T6` and more; `N3` is its `T3`, about a solution rather
than a recast. The book's `T1`, on the length of the output, is not a condition:
`Native.length_of_byLayout` states it in its sharpest form, `o.length + 1 =
((words i).map length).sum + (words i).length`, but it is a consequence of `N1` to
`N3` (an acceptable text is a printed layout, and a printed layout has that length), so
as a condition it would exclude nothing the three do not.

### The two are one relation

Both have the type `Spec`, so "the same relation" can be said as an equality:

```lean
theorem byLayout_eq_byText (M : ℕ) : ByLayout M = ByText M
```

Each has what the other lacks. `ByLayout` is decidable and comes with an induction on
layouts; `ByText` is readable and quantifies over all texts, so it is not decidable on
its face — it becomes so through the equivalence, the layout specification doing work
for the text one. The `←` direction is where Lean's library does the work:
`List.splitOn` reads an acceptable text back into a layout, and `List.intercalate_splitOn`
says that printing that layout gives the text back.

The theorem also settles a question the 2022 defect raises. `N1` to `N3` are conditions
on the printed shape of an output and none of them sees the minimisation: that is the
blind spot the `M3` defect sat in, and the book's own `T1` to `T8` share it. `N4` closes
it, and `byLayout_eq_byText` says it closes it completely — a relation with these four
conditions is *the* relation, so the question "would the conditions have caught the
defect?" has a theorem for an answer rather than a case-by-case argument. The book's
`T1` to `T8` admit no such theorem, and cannot: the `M3`-defective reading of `S1` in
`Meyer/Book/Bug.lean` is provably a different relation and, by the argument above
(mechanised for the inclusion and the witness, argued for the eight properties),
satisfies all eight.

### Against Meyer's

The main result of `Native/Comparison.lean` is that the new specification is the book's:

```lean
theorem byLayout_eq_book (M : ℕ) : ByLayout M = Meyer.Book.Goal M
```

so everything the chapter proves about `S1` holds of `ByLayout` and `ByText`, and, since
`Meyer.Comparison.specifications_differ` separates the book's relation from the paper's,
they differ from the 1985 relation as well; that corollary is not restated. The proof
runs through one observation: a shortest recast of `i` has no two adjacent separators
and none at either end, since `[R]`, `[L]` and `[T]` would each shorten it, and such a
text is the printed form of a cut of its words; every printed cut of the words of `i` is
in turn a shortest recast, reached by exchanging separators and attaining the length
bound of exercise 9-E.6. On a printed cut, `maxline ≤ M` says every line fits and
`new_lines` counts the lines less one, so the book's two minimisations are the layout's
one.

Where the two Meyer specifications differ, over separators at the ends of the text, the
new one sides with the book: a leading or trailing break leaves no trace. One cost is
worth naming: `List.splitOnP` and `List.intercalate` are `noncomputable` reference
models in this toolchain, so the definitions carry that marker. The kernel reduces
both, which is what `decide` needs, but `#eval` does not.

## Alphabets

Neither text fixes the character set, and the two texts assume different things of it.
The paper: "the only property of `CHAR` that matters here is that `CHAR` contains two
elements of particular interest, `blank` and `new_line`". The book:
`CHARACTER ≜ LETTER ∪ SEPARATOR` with `SEPARATOR ≜ {space, new_line}`, `LETTER ≠ ∅` and
`LETTER ∩ SEPARATOR = ∅`. Each is a typeclass in `Meyer/Common.lean`:

```lean
class Alphabet (α : Type*) where          -- 1985
  blank newline : α

class Lettered (α : Type*) extends Alphabet α where   -- 2022
  exists_letter : ∃ c : α, ¬ IsBreak c
```

`Meyer.Paper` and `Meyer.Book` are both stated over `[Alphabet α]` — the book puts the
whole of §9.5 under `LETTER ≠ ∅`, but its definitions do not need a letter, and stating
them without one is a strengthening, not a departure: every statement over `Alphabet`
specialises to `Lettered`. `Native` is concrete over `Char`, which is an instance of
both. Neither class says that `blank` and `new_line` differ, because neither text does.
Making the assumptions explicit turns four remarks into checked facts:

- **`LETTER ≠ ∅` serves exactly one of the book's eight theorems.** `Lettered` occurs in
  the types of exactly two theorems in the repository: `T5`, nondeterminism
  (`Meyer.Book.goal_not_functional`), proved from an abstract letter `c` with the input
  `c cc c` at `M = 4`; and the book's `M3` defect (`Meyer.Book.Bug.goal_unfilled`), which is
  the same input with a third output `c / cc / c`. The 1985 subsequence defect
  (`Meyer.Paper.Bug.domGoal_subset_breaksOnly`) needs no letter and is stated over
  `Alphabet`; its `WHO WHAT WHEN` instance is settled at `Char` in the `Examples` module.
  `T1`–`T4` and `T6`–`T8` are stated and proved over `Alphabet`. The transcriptions never
  mention `Char`; Meyer's own witnesses — `WHO WHAT WHEN`, `␣␣ABC␣␣D␣␣EFG` with its third
  output, `␣AB` — are settled by `decide` in the `Examples` modules, and the paper's
  nondeterminism claim, which the paper makes without any assumption on `CHAR`, is
  stated there at `Char` rather than attributed a letter the paper never asks for.
- **The 1985 specification is the more general, and needs no letter.** Its domain theorem
  holds on every `Alphabet`; on `Bool` with `true` for `blank` and `false` for `new_line`,
  an alphabet with no letters at all, it says that every text has an output
  (`Meyer/Paper/Facts.lean`, section *Letterless*). `Bool` is provably not `Lettered`.
- **Where `blank ≠ new_line` is needed, and where it only seemed to be.** Neither
  specification's definitions need it. Four results do, and take it as a hypothesis:
  the book's remark that `M5` and `M6` define the same function
  (`maxLine_eq_maxRun_letter_or_blank`; if the two separators coincide, `new_line` is a
  space and `M6` counts it); the refutation of the termination argument
  (`recast1_cycle`; the cycle *is* the exchange of the two); `T5` itself, since two
  outputs with the same words can differ only in their separators; and the `M3` defect
  witness, which is `T5`'s input with a third output and inherits both of `T5`'s
  assumptions. The feasibility
  theorem `T8` appeared to need it, because the original proof went through "no spaces
  are left after `owpl`"; the weaker "what is left that is not a new line was never a
  space" suffices and holds regardless. The native round trip through `render` uses it
  at `Char`, where it is a `decide`.
- **The two Meyer specifications differ without a letter.** `Meyer.Comparison.paper_ne_book`
  separates them on the one-character text `[space]` at line limit one, on every
  `Alphabet`: the paper keeps the space and the book deletes it. This mechanises the
  `T7` divergence that was previously a remark, while the `␣AB` example with its empty
  first line is kept at `Char`.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and mathlib version
are pinned.

```sh
lake exe cache get   # mathlib binaries
lake build
```

A clean build produces no warnings and no `sorry`s. To check what the thirty
theorems depend on:

```sh
lake env lean scripts/axioms.lean
```

Each line should report `[propext, Classical.choice, Quot.sound]` or a subset.

## Deviations from the sources

Recorded in full in each module's docstring. In brief:

- Equality of characters is assumed decidable, `[DecidableEq α]`, wherever a definition
  tests it. That is a Lean-side assumption with no counterpart in the texts, whose
  mathematics is classical; it costs no generality, since every type has a classical
  instance, and it is what lets `decide` run on `Char`. The paper's alphabet is
  transcribed as stated; the book's `LETTER ≠ ∅` is deliberately assumed only where a
  letter is used, which strengthens the book's theorems — see [Alphabets](#alphabets).
- "Subsequence" in the paper is `List.Sublist`, for the reason above; in the book it is
  contiguous by definition (§9.2.6) and so is `List.IsInfix`.
- `MAX_SET`/`MIN_SET` and the `mu` operator are rendered as "no element of the set does
  better", in place of Meyer's finiteness side conditions. This agrees with him on
  finite sets and on empty ones, and totalises the partial `MAX_SET` by returning `∅`
  where he would leave it undefined. Over `ℕ` a nonempty set always has a minimum, so
  nothing is lost where only minima are taken. The one place the difference is visible
  is `Meyer/Paper/Bug.lean`, whose docstring says so.
- The book's `M3` is transcribed as its prose describes it, not as its formula reads;
  the formula is the subject of `Meyer/Book/Bug.lean`.
- `WORDS` and `breaks`, which the book leaves to exercise 9-E.6, are taken to be the
  *nonempty* maximal runs. That is the convention `T4` needs. The exercise's uniqueness
  claim about the alternating decomposition is not proved.

## Author

The Lean development is by Vadim Zaliva, [zaliva.org](https://zaliva.org/).
The specifications it transcribes are Meyer's.

AI assistance was used in producing this formalisation. Responsibility for the
results is the author's alone.

## Licence

[MIT No Attribution](https://spdx.org/licenses/MIT-0.html); see `LICENSE`.

## References

- **Naur, Peter.** "Programming by Action Clusters." *BIT* 9(3):250–258, 1969.
- **Goodenough, John B. and Susan L. Gerhart.** "Toward a Theory of Test Data
  Selection." *IEEE TSE* SE-1(2):156–173, 1975; also *Proc. Int. Conf. on Reliable
  Software*, pp. 493–510. Revised as "Toward a Theory of Testing: Data Selection
  Criteria," in R. T. Yeh (ed.), *Current Trends in Programming Methodology, Volume
  II: Program Validation*, Prentice-Hall, 1977, pp. 44–79, the version Meyer analyses.
- **Meyer, Bertrand.** "On Formalism in Specifications." *IEEE Software* 2(1):6–26,
  1985.
- **Meyer, Bertrand.** *Handbook of Requirements and Business Analysis.* Springer,
  2022. Chapter 9.
