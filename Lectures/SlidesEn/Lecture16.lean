/-
Slides of Lecture 16. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Parameter Evaluation" =>

Strict evaluation, call by name, call by need, and the fragment of Unit IV

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-16___-Parameter-Evaluation/)

```lean -show
namespace Slides16
open CoreCpp
```

# §16.1 Strict evaluation

```lean (name := primeiro)
def first : String :=
  "int primeiro(int a, int b) { return a; }
   int main() { return primeiro(1, 10 / 0); }"

#eval (parseProgram first).map run
```
```leanOutput primeiro
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

* The rule `Call` evaluates every argument *before* the body. Used or not, once, effects and errors included.

* C++, Java, Python and Lean are strict. The built in exceptions of Core C++ are `&&`, `||` and `?:`.

# §16.2 Call by name

```tree
f ↦ (τ f (τ₁ name x₁) { c })
ρ_f = [x₁ ↦ thunk(e₁, ρ)]                the unevaluated argument with its environment
ρ_f, σ ⊢ c ⇒ ret v, ρ', σ'
───────────────────────────────────────── (Call-Name)
ρ, σ ⊢ f(e₁) ⇒ v, σ'

ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Name)    every read evaluates e again
ρ, σ ⊢ x ⇒ v, σ'
```

* ALGOL 60. Not in the core. ρ would map a name to a *thunk*, and a read could have effects.

{cite}[P. Naur (ed.), *Revised Report on the Algorithmic Language ALGOL 60*, Communications of the ACM 6(1), 1963.]

# §16.3 Simulating a postponed argument

```lean (name := primeiroPreguicoso)
def firstLazy : String :=
  "int primeiro(int a, std::function<int()> b) { return a; }
   int main() { int z = 0;
   return primeiro(1, [=]() -> int { return 10 / z; }); }"

#eval (parseProgram firstLazy).map run
```
```leanOutput primeiroPreguicoso
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* The closure is the thunk, its copies are the environment ρ₀. The programmer writes the postponement, `[=]() -> int { … }` at the call and `b()` at each use.

# §16.3 Repeated evaluation

```lean (name := duasVezesEfeito)
def twiceEffect : String :=
  "class Caixa { public: int valor; };
   int duasVezes(std::function<int()> t) { return t() + t(); }
   int main() { Caixa* c = new Caixa(); c->valor = 0;
     return duasVezes([=]() -> int {
       c->valor = c->valor + 1; return c->valor; }); }"

#eval (parseProgram twiceEffect).map run
```
```leanOutput duasVezesEfeito
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

* Two calls of the thunk, two effects, 1 + 2. *Call by need*, evaluate once and remember, would give 2.

# §16.4 Lazy evaluation in Haskell

```
primeiro :: Int -> Int -> Int
primeiro a b = a

main = print (primeiro 1 (div 10 0))
```

* Haskell evaluates *by need*. The division never runs, the program prints 1.

```tree
ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Need)    the binding becomes x ↦ v
ρ, σ ⊢ x ⇒ v, σ'
```

* By need equals by name only without effects, which Haskell guarantees. Imperative languages stay strict.

{cite}[S. Peyton Jones, *The Implementation of Functional Programming Languages*, Prentice Hall, 1987.]

# §16.4 The disciplines

:::table +header
*
  * Discipline
  * Argument evaluated
  * Effects
  * Language
*
  * strict, by value
  * once, before the call
  * once, always
  * Core C++, C++, Java, Python, Lean
*
  * by name
  * at each read
  * repeated
  * ALGOL 60
*
  * by need
  * at the first read, if any
  * once, if read
  * Haskell
*
  * closure as thunk
  * at each call of the closure
  * at each call
  * simulation in Core C++
:::

# §16.5 The fragment of Unit IV

:::table +header
*
  * Construction
  * Rules
*
  * call by value, `return`
  * `T-Call`, `Call`, `Return`
*
  * reference parameters `τ& x`
  * `T-Call` with ⊢ₗ, `Call` with an alias binding
*
  * `std::function<τ(…)>`, lambdas `[=]`
  * `T-Lambda`, `Lambda`
*
  * calls of function values
  * `T-CallFn`, `CallFn`
*
  * capture by copy, read only
  * `T-LocVar` with the read only mark
:::

```lean (name := functionValue)
def functionValue : String :=
  "int main() {
   std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
   std::function<int(int, int)> h = g; return h(10, 3); }"

#eval (parseProgram functionValue).map run
```
```leanOutput functionValue
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

# Summary

* Core C++ is *strict*, every argument is evaluated once before the call, with `&&`, `||` and `?:` as the non strict exceptions.

* *Call by name* re-evaluates the argument at each read, *call by need* evaluates it once at the first read. Neither is in the core.

* A closure of no parameters *simulates* a postponed argument, and shows the repeated effects of call by name.

* Haskell is lazy and pure, so by need and by name coincide there.

* Unit IV gave Core C++ call by value and by reference, lambdas, closures and function values, each with its rule.

Exercises: see the [lecture notes](../en/Lecture-16___-Parameter-Evaluation/).

```lean -show
end Slides16
```
