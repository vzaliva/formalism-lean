import Native.Spec
import Native.Properties
import Native.Check
import Native.Comparison

/-!
# Native

A Lean-native specification of the text-formatting problem, alongside the two
transcriptions of Meyer's in `Meyer`.

* `Native.Spec` -- the specification twice over: `ByLayout`, by way of layouts,
  and `ByText`, on the output text, by four conditions read off it.
* `Native.Properties` -- what is proved on the native side: decidability,
  feasibility, nondeterminism, and that the two formulations are the same
  relation.
* `Native.Check` -- a linear-time decision procedure for it.
* `Native.Comparison` -- it is the same relation as the book's, which
  `Native.Check` therefore decides as well.
-/
