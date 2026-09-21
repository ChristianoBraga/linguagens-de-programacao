/-
Slides of Lecture 27. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "The Functional Paradigm" =>

The fragment without update, and the store written once

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-27___-The-Functional-Paradigm/)

```lean -show
namespace Slides27
open CoreCpp
```

# §27.1 The fragment

::::cols
:::col
{lbl}[Admitted]

* `int`, `bool`, `void`, `std::function`

* literals, variable, operators, the conditional

* function call, call through a function value

* the lambda `[=]`

* declaration, block, `if`, `return`
:::
:::col
{lbl}[Forbidden]

* assignment

* `while`, `for`, expression statement

* the local reference, the reference parameter

* class, method call, `this`

* `new`, `delete`, pointers, vectors
:::
::::

* A declaration is not a variable here, it is a *let binding*, because nothing can write the location afterwards.

# §27.1 The checker runs

```lean (name := funCheck)
def escala : String :=
  "int soma(int n) {
     return n == 0 ? 0 : n + soma(n - 1);
   }
   std::function<int(int)> escala(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int aplica(std::function<int(int)> f, int v) {
     return f(v);
   }
   int main() {
     std::function<int(int)> triplo = escala(3);
     int s = soma(4);
     return aplica(triplo, s);
   }"

#eval (parseProgram escala).map fun p => (fragment .functional p, run p)
```
```leanOutput funCheck
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* A recursive function, one that returns a closure and one that takes one. Between them, the whole paradigm.

# §27.2 The store is written once

* The whole language writes σ in three places, `Assign`, the constructor of a `new` and the destructor of a `delete`. The fragment has *none of the three*.

* A location receives its value at its declaration or parameter binding and *is never written again*.

* Not the same as saying σ does not change. A call still allocates and releases. The claim is that *no location holds two values in its life*.

# §27.2 Two consequences

* *Referential transparency.* One expression, twice, under the same ρ and σ, gives the same value. A name may be replaced by what it denotes.

* *Indifference to the evaluation order.* Neither operand of `e₁ ⊕ e₂` can change σ where the other reads, so left to right and right to left agree.

* A program of the fragment therefore has *one meaning* under Core C++ and under any C++ compiler.

* The price. No data structure, no update in place. The fragment is the paradigm *in miniature*.

# §27.3 Recursion in place of iteration

```lean (name := caseFun)
def caseFun : String :=
  "int somaAte(std::function<bool(int)> p, int n) {
     return n == 0 ? 0 : (p(n) ? n : 0) + somaAte(p, n - 1);
   }
   int main() {
     std::function<bool(int)> par = [=](int i) -> bool { return i % 2 == 0; };
     return somaAte(par, 10);
   }"

#eval (parseProgram caseFun).map fun p => (fragment .functional p, run p)
```
```leanOutput caseFun
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* The loop with an accumulator becomes a function with an accumulating parameter, and the *invariant becomes the specification*.

* A recursion of depth ten puts ten frames in σ. No tail call elimination here.

# §27.4 Where Core C++ stops

* *Immutable data.* A Haskell list is built once and shared. The fragment has no data at all.

* *Laziness.* Call by name was a rule without a counterpart. Haskell evaluates by need, so an infinite list is usable.

* *Algebraic data types.* A sum type with a `case` is what the class hierarchy and dispatch do. The two are dual, easy to extend with cases against easy to extend with operations.

* None of the three changes the semantics. Saying so plainly beats stretching the core to imitate them.

# Summary

* The functional fragment *forbids the update*, the loops and the heap, and keeps the expressions, the lambdas and the calls.

* Its store is *written once*, which is the strongest property of the three fragments.

* From it, *referential transparency* and indifference to the evaluation order.

* Iteration becomes recursion, and the loop invariant becomes the specification of a function.

* Immutable data, laziness and pattern matching are Haskell, and the course says so instead of pretending.

Exercises: see the [lecture notes](../en/Lecture-27___-The-Functional-Paradigm/).

```lean -show
end Slides27
```
