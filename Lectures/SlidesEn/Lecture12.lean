/-
Slides of Lecture 12. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Expressions with Side Effects" =>

Effects through calls, the evaluation orders and the alternative derivation

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-12___-Expressions-with-Side-Effects/)

```lean -show
namespace Slides12
open CoreCpp
```

# §12.1 Effects through calls

```lean (name := proxDef)
def counter : String :=
  "class Cell { public: int n; };
   int next(Cell* c) {
     c->n = c->n + 1;
     return c->n;
   }
   int main() {
     Cell* c = new Cell();
     return next(c) + 10 * next(c);
   }"

#eval (parseProgram counter).map run
```
```leanOutput proxDef
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* The two calls return 1 and 2. Left first gives 1 + 10 · 2 = 21, right first gives 2 + 10 · 1 = 12.

* *The order is part of the meaning of* `+`.

# §12.2 The orders Core C++ fixes

:::table +header
*
  * Construction
  * Order
  * Rule
  * C++17
*
  * `e₁ ⊕ e₂`
  * left, then right
  * `Binary`
  * unspecified
*
  * `f(e₁, …, eₖ)`
  * left to right
  * `Call`
  * unspecified
*
  * `e₁ = e₂`
  * right, then left
  * `Assign`
  * fixed
*
  * `e[i]`
  * vector, then index
  * `LocIndex`
  * fixed
*
  * `&&`, `||`, `?:`
  * left, then only if needed
  * `And`, `Or`, `Cond`
  * fixed
:::

* Two decisions of Core C++, four orders kept from C++17. The order lives in the *order of the premises*.

# §12.3 The alternative derivation

```tree
ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂

ρ, σ ⊢ e₂ ⇒ v₂, σ₁    ρ, σ₁ ⊢ e₁ ⇒ v₁, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary-RL)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

* A C++ compiler may apply `Binary-RL`. Both derivations are valid for C++17, the standard does not choose. *Nondeterminism*.

* Core C++ has one rule and one result. `call_order.cpp` returns 21 here, 21 or 12 under `g++`.

# §12.3 Assignment and arguments

```lean (name := assignOrder)
def assignOrder : String :=
  "class Cell { public: int n; };
   int next(Cell* c) { c->n = c->n + 1; return c->n; }
   int main() {
     Cell* c = new Cell();
     std::vector<int>* v = new std::vector<int>(3);
     (*v)[next(c)] = next(c);
     return (*v)[1] * 10 + (*v)[2];
   }"

#eval (parseProgram assignOrder).map run
```
```leanOutput assignOrder
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* Right side first, `next(c)` is 1 there. The index is evaluated afterwards and is 2. Index 2 receives 1.

* Arguments left to right, `f(next(c), next(c))` is `f(1, 2)`.

# §12.4 Why not forbid effects in expressions

* Fidelity to C++, where a call inside an expression is ordinary.

* The rules already thread the store through expressions, ρ, σ ⊢ e ⇒ v, σ′, since Lecture 3. *No rule was rewritten* to admit effects.

* What the rules fix is the *order*. A side effect is a feature the semantics must describe completely, and completely means choosing an order.

# §12.5 The fragment so far

* Types `int`, `bool`, `void`, classes with fields, pointers, `std::vector<τ>`.

* Expressions with literals, variables, operators, conditional, `new`, field access, dereference, indexing, calls.

* Commands with declaration, reference declaration, assignment, block, `if`, `while`, `for`, `return`.

* Functions with call by value. Twenty three examples agreeing with `g++` wherever C++ is defined.

* Unit IV adds parameters by reference, lambdas and `std::function`, and call by name with Haskell as contrast.

# Summary

* An expression has a *side effect* only through a call, and then the *order of evaluation* is part of its meaning.

* Core C++ fixes every order in the order of the premises. Left to right where C++17 is unspecified, the C++17 order where it is fixed.

* The *alternative derivation* `Binary-RL` is valid C++ and absent from Core C++. One rule, one result.

* Effects stay in the language because the store was threaded through expressions from the start.

Exercises: see the [lecture notes](../en/Lecture-12___-Expressions-with-Side-Effects/).

```lean -show
end Slides12
```
