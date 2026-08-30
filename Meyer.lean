import Meyer.Common
import Meyer.Char
import Meyer.Paper.Spec
import Meyer.Paper.Lemmas
import Meyer.Paper.Retention
import Meyer.Paper.Facts
import Meyer.Paper.Bug
import Meyer.Paper.Examples
import Meyer.Book.Spec
import Meyer.Book.Recast
import Meyer.Book.Words
import Meyer.Book.Facts
import Meyer.Book.Bug
import Meyer.Book.Examples
import Meyer.Comparison
import Meyer.Comparison.Examples

/-!
# formalism-lean

Bertrand Meyer's two formal specifications of the text-formatting problem, with
the results each text states about its own: his two claims from 1985, and `T1` to
`T8` from the 2022 chapter.

* `Meyer.Common` -- the vocabulary the two share, and their two alphabet
  assumptions as typeclasses; `Meyer.Char` instantiates both at `Char`.
* `Meyer.Paper` -- *On Formalism in Specifications*, IEEE Software 2(1), 1985.
* `Meyer.Book` -- *Handbook of Requirements and Business Analysis*, Springer,
  2022, chapter 9 section 9.5.
* `Meyer.Comparison` -- the two are not the same relation.

The transcriptions are stated over an abstract alphabet and never mention
`Char`; each has an `Examples` module where Meyer's own worked examples are
settled at `Char` by `decide`.

Importing this module brings in everything.  `README.md` carries the narrative.
-/
