/-
Slides of Lecture 14. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Call by Reference" =>

Reference parameters, swap, aliasing and what C++ leaves undefined

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-14___-Call-by-Reference/)

```lean -show
namespace Slides14
open CoreCpp
```

# §14.1 A parameter bound to a location

* `void inc(int& r)`. The parameter `r` is a name for the *location of the argument*, as the local reference `int& y = x` of Unit III.

* The argument must denote a location. A variable, a field, `*p`, a vector element. Not a literal, not an arithmetic result.

* In the function environment the binding is an *alias*, and the return does not free it.

# §14.1 The call rule with both mechanisms

```tree
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
for each i, left to right, σ'₀ = σ,
  pᵢ = τᵢ     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)     by value
  pᵢ = τᵢ&    ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ                              by reference
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
─────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_f))
```

* One premise differs. ⇒ and alloc for a value, ⇒ₗ and no allocation for a reference. Copies and locals leave, referents stay.

# §14.2 Swap

```lean (name := swap)
def swap : String :=
  "void swap(int& a, int& b) { int t = a; a = b; b = t; }
   int main() { int x = 1; int y = 2; swap(x, y);
     return x * 10 + y; }"

#eval (parseProgram swap).map run
```
```leanOutput swap
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* The environment of `swap` is \[a ↦ ℓ0, b ↦ ℓ1\], the locations of `x` and `y` under new names. The writes reach `main`.

* By value the same body would exchange two copies and return 12.

# §14.3 Any location is an argument

```lean (name := incField)
def incrementField : String :=
  "class P { public: int a; };
   void inc(int& r) { r = r + 1; }
   int main() { P* p = new P(); inc(p->a); inc(p->a);
     std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
     return p->a * 10 + (*v)[1]; }"

#eval (parseProgram incrementField).map run
```
```leanOutput incField
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* A field and a vector element denote locations, and `inc` changes them in place.

# §14.3 What is rejected

```lean (name := incLit)
def incrementLiteral : String :=
  "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }"

#eval (parseProgram incrementLiteral).map check
```
```leanOutput incLit
Except.ok (Except.error (CoreCpp.TypeError.refArgument "inc" "r" (CoreCpp.Expr.intLit 5)))
```

```tree
Γ ⊢ eᵢ : τᵢ' with τᵢ' ≈ τᵢ for pᵢ = τᵢ    Γ ⊢ₗ eⱼ : τⱼ for pⱼ = τⱼ&
────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

* The argument of a reference parameter is checked with ⊢ₗ and must have *exactly* the parameter type.

# §14.4 Aliasing between parameters

```lean (name := dup)
def duplicate : String :=
  "void dup(int& a, int& b) { a = a + b; b = b + a; }
   int main() { int x = 1; dup(x, x); return x; }"

#eval (parseProgram duplicate).map run
```
```leanOutput dup
Except.ok (Except.ok (CoreCpp.Val.int 4))
```

* `dup(x, x)` binds `a` and `b` to one location. Each write changes what the other reads, 4 instead of 3.

* The price of call by reference. A body cannot assume two reference parameters are independent.

# §14.5 What C++ leaves undefined

:::table +header
*
  * Situation
  * C++17
  * Core C++
*
  * `inc(5)`
  * compilation error
  * type error
*
  * `const int& r = 5`
  * allowed, temporary extended
  * excluded
*
  * reference returned to a dead local
  * undefined
  * impossible, no reference results
*
  * reference to a freed object
  * undefined
  * `error`, location outside σ
*
  * two references to one argument
  * aliasing, defined
  * aliasing, defined
:::

# Summary

* A `τ&` parameter is bound to the *location* of its argument, an alias binding, nothing allocated, nothing freed on return.

* The argument must denote a location of exactly the parameter type, checked with ⊢ₗ.

* Swap works because the parameters *are* the arguments.

* Two reference parameters may *alias* one location, as in C++.

* Core C++ has no reference results and no dead references, so the undefined cases of C++ do not arise.

Exercises: see the [lecture notes](../en/Lecture-14___-Call-by-Reference/).

```lean -show
end Slides14
```
