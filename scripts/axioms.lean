import Meyer
import Native

/-!
# Axiom audit

Every `theorem` in the development, which is to say every claim either of
Meyer's sources makes about its own specification, every finding this
development asserts on its own account, and the claims made about the
Lean-native specification in `Native`.  Run with

```sh
lake env lean scripts/axioms.lean
```

Each line should report `[propext, Classical.choice, Quot.sound]` or a subset of
it.  Anything else means an axiom has crept in.
-/

#print axioms Meyer.Paper.Bug.singleBreaks_subset
#print axioms Meyer.Paper.Bug.compacted_eq_empty
#print axioms Meyer.Paper.Bug.domGoal_ne_noOversizeWord
#print axioms Meyer.Paper.goal_not_functional
#print axioms Meyer.Paper.trimmed_nonempty_iff
#print axioms Meyer.Paper.domGoal_eq_noOversizeWord
#print axioms Meyer.Paper.sameWords_of_mem_compacted
#print axioms Meyer.Book.Bug.newLines_le_one
#print axioms Meyer.Book.Bug.solutions_subset
#print axioms Meyer.Book.Bug.goal_unfilled
#print axioms Meyer.Book.mu_nonempty_iff
#print axioms Meyer.Book.maxWord_le_maxLine
#print axioms Meyer.Book.maxLine_eq_maxRun_letter_or_blank
#print axioms Meyer.Book.solution_not_isSeparator_at_ends
#print axioms Meyer.Book.solutions_of_forall_isSeparator
#print axioms Meyer.Book.feasibility
#print axioms Meyer.Book.goal_not_functional
#print axioms Meyer.Book.recast1_cycle
#print axioms Meyer.Book.length_le_of_recast
#print axioms Meyer.Book.words_eq_of_recast
#print axioms Meyer.Book.length_breaks_ge
#print axioms Meyer.Comparison.specifications_differ
#print axioms Meyer.Comparison.paper_ne_book
#print axioms Native.feasibility
#print axioms Native.byLayout_not_functional
#print axioms Native.byLayout_of_forall_isBreak
#print axioms Native.byLayout_eq_book
#print axioms Native.length_le_of_byLayout
#print axioms Native.length_of_byLayout
#print axioms Native.byLayout_eq_byText
#print axioms Native.byText_iff_minSet
