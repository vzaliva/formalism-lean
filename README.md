# formalism-lean

A Lean 4 formalisation of the formal specification given in

> Bertrand Meyer, *On Formalism in Specifications*, IEEE Software 2(1):6–26, 1985.
> [DOI 10.1109/MS.1985.229776](https://doi.org/10.1109/MS.1985.229776) ·
> [free PDF](https://se.inf.ethz.ch/~meyer/publications/ieee/formalism.pdf)

Meyer's paper argues that natural language is inadequate for specification, and
makes the case on a text-formatting problem, word wrap, with a long and
uncomfortable history:

- **Naur (1969)** poses the problem, gives a program, and gives a *proof* that the
  program satisfies it.
- **Goodenough & Gerhart (1975)** find seven errors in that proved program.
  Concluding the specification was at fault, they write a new one, four times
  longer, and revise it again in 1977.
- **Meyer (1985)** takes that carefully rewritten specification and exhibits six
  of his seven "sins of the specifier" in it, then gives a formal specification
  of his own, and derives from it a theorem nobody had written down in prose: the
  problem has no solution when the input contains a word longer than `MAXPOS`.

This repository transcribes Meyer's formal specification into Lean and proves the
two claims he makes about it. Everything is **sorry-free** and depends only on
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

As far as we can find (literature, arXiv, and public repositories), this
specification had not previously been formalised in any proof assistant.

## Modules

| Module | Contents |
|---|---|
| `Meyer/Spec.lean` | the specification: `SINGLE_BREAKS`, `COMPACTED`, `EQUIVALENT`, `TRIMMED`, `FEWEST_LINES`, `goal`. Definitions only |
| `Meyer/Lemmas.lean` | basic API: bounds on `max_line_length`, nonemptiness of `MIN_SET`/`MAX_SET`, break-substitution |
| `Meyer/Retention.lean` | the step Meyer asserts without proof: compacting a text does not change its words |
| `Meyer/Facts.lean` | Meyer's two claims, proved |
| `Meyer/Bug.lean` | a defect in the paper, proved (see below) |

The headline results, both in `Meyer/Facts.lean`:

```lean
theorem goal_not_functional :
    ∃ (n : ℕ) (i o₁ o₂ : Text), Goal n i o₁ ∧ Goal n i o₂ ∧ o₁ ≠ o₂

theorem domGoal_eq_noOversizeWord : DomGoal MAXPOS = NoOversizeWord MAXPOS
```

## What formalising it turned up

**1. The definition of "subsequence" is wrong as written.** Meyer defines a
subsequence of `s` as `s ∘ u` for `u` a *sorted* sequence of positions, and
defines sorted with a non-strict `≤`. So a position may repeat: in his own
example `<a b a a b d c d>`, the index sequence `<3 3 3 3>` is sorted, making
`<a a a a>` a "subsequence", and a run of any length qualifies just as well. But
`COMPACTED (a)` is the set of *longest* members of `SINGLE_BREAKS (a)`, and with
repetition there is no longest, so `COMPACTED (a)` is empty and `goal` relates
nothing to anything.

`Meyer/Bug.lean` formalises the literal reading and proves it contradicts
Meyer's own domain theorem, so the strict reading is *forced*, not merely
preferable. Note which half is at fault. His informal gloss, "a sequence made of
zero or more of the elements of `s`, in the same order as in `s`", is correct;
the formal definition printed beside it is what admits repetition. In a paper
arguing that formalism repairs the imprecision of prose, the prose was right and
the formalism was wrong.

**2. The step the theorem rests on is a parenthesis, and its obvious proof does
not work.** Meyer's domain theorem needs to know that compacting a text leaves
its *words* alone. He asserts it in an aside (omit a non-break character and it
could be reinserted to give a longer member of `SINGLE_BREAKS`) and moves on.
His own sentence states the solvability condition in terms of the *compacted*
text and then states the theorem about the *input*; this is the silent bridge.

The argument is sound in outline, but the induction it suggests fails: maximality
of `b` in `a` does not hand down maximality of `b`'s tail in `a`'s tail. For
`a = "  x"` the compaction is `b = " x"`; after keeping the first blank the
residual problem is `"x"` against `" x"`, which `" x"` wins. `Meyer/Retention.lean`
repairs it with a second invariant, in force exactly when a break has just been
emitted, under which competitors must additionally not begin with a break. The
two invariants alternate through the induction, and their conclusions have to be
asymmetric: the unconstrained one controls prefixes as well as infixes, and the
prefix half genuinely fails under the constrained one.

**3. Nothing else was wrong.** Both of Meyer's claims are true, and the rest of
the specification transcribes without incident. Keep (1) and (2) apart, though:
one is an error, the other is ordinary compression of a correct argument.
Formalisation surfaces both.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and mathlib
version are pinned.

```sh
lake exe cache get   # mathlib binaries
lake build
```

A clean build produces no warnings and no `sorry`s.

## Deviations from the paper

Recorded in full in each module's docstring. In brief: `CHAR` is instantiated at
Lean's `Char` (Meyer keeps it abstract, noting only `blank` and `new_line`
matter); "subsequence" is `List.Sublist`, for the reason above; and `MAX_SET` /
`MIN_SET` are rendered as "no element does better", which agrees with Meyer
wherever the extremum exists and is empty otherwise, in place of his finiteness
side condition.

## References

- **Naur, Peter.** "Programming by Action Clusters." *BIT* 9(3):250–258, 1969.
- **Goodenough, John B. and Susan L. Gerhart.** "Toward a Theory of Test Data
  Selection." *IEEE TSE* SE-1(2):156–173, 1975. Revised in *Current Trends in
  Programming Methodology* vol. 2, Prentice-Hall, 1977, pp. 44–79, the version
  Meyer analyses.
- **Meyer, Bertrand.** "On Formalism in Specifications." *IEEE Software*
  2(1):6–26, 1985.
