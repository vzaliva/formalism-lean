import Meyer.Common

/-!
# `Char` as an alphabet

Lean's `Char` is an alphabet of both of Meyer's kinds, with `' '` for `blank` and
`'\n'` for `new_line`.  Nothing in the transcriptions of the two texts depends
on it: `Meyer.Paper`, `Meyer.Book` and `Meyer.Comparison` are stated over an
abstract alphabet and never mention `Char`.  It is where the worked examples
live (`Meyer.Paper.Examples`, `Meyer.Book.Examples`, `Meyer.Comparison.Examples`),
because `decide` can settle a concrete text, and it is the alphabet of the
native specification, `Native.Spec`.
-/

namespace Meyer

/-- `Char` is an alphabet of the paper's kind ... -/
instance : Alphabet Char := ⟨' ', '\n'⟩

/-- ... and of the book's. -/
instance : Lettered Char where
  exists_letter := ⟨'a', by decide⟩

/-- On `Char` the two separators differ.  Neither class asserts this; it is what
the results that need it (`M5 = M6`, `T5`, the termination cycle, the native
round trip) get from `Char`. -/
lemma blank_ne_newline : (blank : Char) ≠ newline := by decide

end Meyer
