import Native.Spec
import Native.Properties
import Native.Comparison

/-!
# Native

A Lean-native specification of the text-formatting problem, alongside the two
transcriptions of Meyer's in `Meyer`.

* `Native.Spec` -- the specification, and the properties `N1` to `N4` expected
  of its outputs.
* `Native.Properties` -- what is proved about it on its own: decidability,
  feasibility, nondeterminism, `N1` to `N4`, and that the four are `Goal`.
* `Native.Comparison` -- it is the same relation as the book's.
-/
