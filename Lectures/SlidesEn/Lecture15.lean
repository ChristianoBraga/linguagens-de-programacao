/-
Slides of Lecture 15. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lambdas and Closures" =>

Functions as values, capture by copy and calls through std::function

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-15___-Lambdas-and-Closures/)

```lean -show
namespace Slides15
open CoreCpp
```

# §15.1 Functions as values

* So far a function is a *declaration*, named once, called by name, never stored or passed.

* `std::function<τ(τ₁, …, τₖ)>` is the type of *function values*. A variable holds one, a parameter receives one, a function returns one.

* Values come from *lambda expressions*. `[=]` is the capture clause, copies of the variables the body uses.

```
[=](int x) -> int { return k * x; }
```

# §15.2 Where a lambda occurs

:::table +header
*
  * Position
  * Expected type from
*
  * initialiser, `std::function<int(int)> f = [=]…`
  * the declared type
*
  * argument, `apply([=]…, 3)`
  * the parameter type
*
  * `return [=]…`
  * the result type of the function
:::

* No closure type of its own. The lambda is checked *against* the `std::function` of its position, Γ ⊢ e ◁ τ.

```lean (name := autoLambda)
def autoLambda : String :=
  "int main() { auto f = [=](int x) -> int { return x; };
   return f(1); }"

#eval parseProgram autoLambda
```
```leanOutput autoLambda
Except.error "syntax error at token 8 ('[=]'): expected primary expression"
```

# §15.2 Typing a lambda

```tree
Γ' = Γ marked read only, [x₁ ↦ τ₁, …, xₖ ↦ τₖ]    Γ' ⊢ c ⊣ Γ''
──────────────────────────────────────────────────────────────── (T-Lambda)
Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>
```

* Parameter and result types *exactly* those of the expected type.

* The body sees the enclosing variables as *read only*, they will be copies.

```lean (name := constCapture)
def constCapture : String :=
  "int main() { int n = 1;
   std::function<int()> f = [=]() -> int { n = 2; return n; };
   return f(); }"

#eval (parseProgram constCapture).map check
```
```leanOutput constCapture
Except.ok (Except.error (CoreCpp.TypeError.constCapture "n"))
```

# §15.3 The closure

```tree
{y₁, …, yₘ} = free variables of c bound in ρ, minus the xᵢ
ρ(yⱼ) = ℓⱼ    ℓⱼ ∈ dom σ    wⱼ = σ(ℓⱼ)
────────────────────────────────────────────────────────────────── (Lambda)
ρ, σ ⊢ [=](x⃗) -> τ { c } ⇒ closure(x⃗, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ
```

* The closure holds *values*, copied at the lambda. A later write to `n` is not seen.

```lean (name := captureCopy)
def captureCopy : String :=
  "int main() { int n = 5;
   std::function<int(int)> sum = [=](int x) -> int { return x + n; };
   n = 100; return sum(1); }"

#eval (parseProgram captureCopy).map run
```
```leanOutput captureCopy
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

# §15.4 Calling a function value

```tree
ρ, σ ⊢ e ⇒ closure(x⃗, τ, c, [y⃗ ↦ w⃗]), σ₀    ρ, σᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ
(ℓ'ⱼ, ·) = alloc(wⱼ)    (ℓᵢ, ·) = alloc(vᵢ)
ρ_c = [y⃗ ↦ ℓ⃗', x⃗ ↦ ℓ⃗]    ρ_c, σ' ⊢ c ⇒ ret v, ρ'', σ''
──────────────────────────────────────────────────────────── (CallFn)
ρ, σ ⊢ e(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓ'ⱼ, ℓᵢ} ∪ (ρ'' ∖ ρ_c))
```

* Fresh locations for the copies and the parameters, an environment with *only them*, everything freed on return.

* `f(…)` with `f` a variable of function type is this rule. A local hides a function of the same name.

# §15.5 Higher order functions

```lean (name := multiplier)
def multiplier : String :=
  "std::function<int(int)> multiplier(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int apply(std::function<int(int)> f, int v) { return f(v); }
   int main() { return apply(multiplier(3), 14); }"

#eval (parseProgram multiplier).map run
```
```leanOutput multiplier
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* The closure outlives the call of `multiplier`. Its copy of `k` is *inside* the closure, nothing dangles.

# §15.6 Effects through a captured pointer

```lean (name := counter)
def counter : String :=
  "class Box { public: int value; };
   std::function<int()> counter() {
     Box* c = new Box();
     c->value = 0;
     return [=]() -> int { c->value = c->value + 1; return c->value; };
   }
   int main() { std::function<int()> k = counter();
     int first = k(); return k() + k() + first; }"

#eval (parseProgram counter).map run
```
```leanOutput counter
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

* The copy of `c` is the *same location*. The object lives in σ, so every call updates it. This is how a closure keeps state.

# §15.7 Why only capture by copy

:::table +header
*
  * Capture
  * The closure holds
  * After the block ends
*
  * `[=]` on an `int`
  * a copy of the value
  * safe
*
  * `[=]` on a pointer
  * a copy of a location of an object
  * safe, the object lives in σ
*
  * `[&]`, excluded
  * the location of the variable
  * undefined in C++
:::

* No closure of Core C++ can hold a dangling location. The rule `Lambda` reads σ and stores what it read.

# Summary

* `std::function<τ(…)>` types have *closures* as values, made by lambdas `[=]` in three positions.

* A lambda has no type of its own, it is checked *at* the expected type, Γ ⊢ e ◁ τ, with the enclosing variables read only.

* A closure holds *copies*, taken at the lambda. A captured pointer still reaches its object.

* A call through a function value allocates copies and parameters afresh and frees them on return.

* `[&]` is excluded, so no closure dangles.

Exercises: see the [lecture notes](../en/Lecture-15___-Lambdas-and-Closures/).

```lean -show
end Slides15
```
