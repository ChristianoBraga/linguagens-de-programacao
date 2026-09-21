/-
Slides of Lecture 13. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Functions and Call by Value" =>

Abstraction, the call rule, copies and the return control

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-13___-Functions-and-Call-by-Value/)

{cite}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, chapter 5.]

```lean -show
namespace Slides13
open CoreCpp
```

# §13.1 Abstraction

* An *abstraction* gives a name and parameters to a piece of program.

* A *function* abstracts an expression, its call yields a value. A *procedure* abstracts a command, its call has an effect on σ. Core C++ writes both as functions, `void` for the second.

* *Parameters* are the names the body uses, *arguments* are the expressions the call supplies. The *parameter mechanism* relates them.

* Unit I fixed one mechanism, *call by value*. This unit writes its rule, adds call by reference, functions as values, and compares with other disciplines.

# §13.2 The call rule

```tree
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })
ρ, σ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ            arguments, left to right
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, vᵢ),  σ'₀ = σₖ                  a fresh location with a copy
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                            only the parameters
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓ₁, …, ℓₖ}              the copies leave
```

* Arguments first, effects kept. Then a *fresh location* per value. The body sees *only the parameters*, there are no globals. The return frees the copies.

# §13.2 Typing a call

```tree
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ' with τᵢ' ≈ τᵢ
────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

```lean (name := square)
def square : String :=
  "int square(int n) { return n * n; }
   int main() { int a = 6; return square(a + 1); }"

#eval (parseProgram square).map run
```
```leanOutput square
Except.ok (Except.ok (CoreCpp.Val.int 49))
```

* The argument `a + 1` is evaluated to 7 before the body runs.

# §13.3 The parameter is a copy

```lean (name := twice)
def double : String :=
  "int twice(int n) { n = n * 2; return n; }
   int main() { int x = 21; return twice(x) + x; }"

#eval (parseProgram double).map run
```
```leanOutput twice
Except.ok (Except.ok (CoreCpp.Val.int 63))
```

* `twice` writes to `n`, the copy at a fresh location. `x` of `main` keeps 21, and the result is 42 + 21.

* In the trace the body runs under \[n ↦ ℓ1\], and after the call the store is back to \{ℓ0 ↦ 21\}.

# §13.4 Return as control

* `return e` yields the control *ret v*. `Seq-Ret`, `While-Ret`, `if` and blocks propagate it upwards. Only the call turns it back into a value.

* A body that ends with *normal* has not returned. `void` function, the value is void. Other functions, `error`.

```lean (name := semRetorno)
def noReturn : String :=
  "int f(int n) { if (n > 0) { return 1; } }
   int main() { return f(0); }"

#eval (parseProgram noReturn).map run
```
```leanOutput semRetorno
Except.ok (Except.error (CoreCpp.Error.missingReturn "f"))
```

* The type checker does not see it, that would need a flow analysis. C++ leaves it undefined, Core C++ gives `error`.

# §13.5 Static checking of calls

```lean (name := callType)
def wrongArgument : String :=
  "int f(int n) { return n; } int main() { return f(true); }"

#eval (parseProgram wrongArgument).map check
```
```leanOutput callType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument n of f" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

* The function exists, the arity matches, each argument has the type of its parameter, `nullptr` against a pointer as the only tolerance.

* Inside the body the parameters are the whole initial context, and `return` is checked against the result type, rule `T-Fun`.

# Summary

* Functions abstract expressions, procedures abstract commands, both are functions in Core C++.

* *Call by value*. Arguments left to right, a fresh location with a copy per parameter, a body that sees only the parameters, copies freed on return.

* A write to a parameter never reaches the argument.

* `return` is a *control result* consumed by the call. A body that ends without it is `error` unless `void`.

* Calls are checked statically, arity and argument types.

Exercises: see the [lecture notes](../en/Lecture-13___-Functions-and-Call-by-Value/).

```lean -show
end Slides13
```
