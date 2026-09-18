/-
Bibliography for the lecture notes. References that Verso's citation types
can express live here. Books are cited in margin notes with the full
reference, because Verso has no `Book` type.
-/
import VersoManual
open Verso.Genre.Manual

def kahn1987 : InProceedings where
  title := inlines!"Natural Semantics"
  authors := #[inlines!"Gilles Kahn"]
  year := 1987
  booktitle := inlines!"STACS 87"
  series := some <| inlines!"Lecture Notes in Computer Science, vol. 247, pp. 22–39, Springer"
  url := some "https://inria.hal.science/inria-00075953"
