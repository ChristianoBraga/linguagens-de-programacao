/-
Slides of Lecture 5. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Values and Types" =>

The typing judgment, the context Γ and what a type system buys

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-5___-Values-and-Types/)

```lean -show
namespace Slides5
open CoreCpp
```

# §5.1 Values and types

* A *value* is a datum a program computes, stores, passes and returns.

* A *type* is a set of values with the operations that apply to them. `int` is the 32 bit integers with arithmetic and order, `bool` the two truth values with the connectives.

* An operation on a value outside its type has *no meaning*. A language rejects the program, stops it, or lets the machine read the bits.

* *Primitive* types have atomic values, *composite* types build values from values, *recursive* types contain themselves.

# §5.1 The types of Unit II

:::table +header
*
  * Kind
  * Types
  * Values
*
  * primitive
  * `int`, `bool`
  * 32 bit integers, `true`, `false`
*
  * composite
  * `class C` with fields
  * records of locations, reached through `C*`
*
  * recursive
  * `class No` with a field `No*`
  * finite chains of records
*
  * composite
  * `std::vector<int>`
  * sequences of locations, reached through a pointer
:::

# §5.2 The typing judgment

* Γ ⊢ e : τ, the expression e has type τ in the *context* Γ, a finite map from identifiers to types.

* Γ is the static counterpart of ρ. A declaration puts x in Γ, every later use reads its type there. *No store*, types exist before values.

```tree
─────────────── (T-Lit)      ─────────────── (T-BoolLit)      Γ(x) = τ
Γ ⊢ n : int                  Γ ⊢ b : bool                     ─────────── (T-Var)
                                                              Γ ⊢ x : τ

Γ ⊢ e₁ : int    Γ ⊢ e₂ : int                Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)      ──────────────────────────── (T-Rel)
Γ ⊢ e₁ ⊕ e₂ : int                           Γ ⊢ e₁ ⋈ e₂ : bool
```

# §5.2 Equality and the conditional

```tree
Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    τ₁ ≈ τ₂    τ₁, τ₂ have values
──────────────────────────────────────────────────────── (T-Eq)
Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ has values
─────────────────────────────────────────────────────── (T-Cond)
Γ ⊢ e₁ ? e₂ : e₃ : τ
```

* τ₁ ≈ τ₂ is equality until pointers arrive, then it also accepts `nullptr` against a pointer.

* "τ has values" excludes `void` and, from Lecture 6 on, the *object types*.

# §5.2 A typing derivation

{exh}[x + 1 < 10 with Γ = \[x ↦ int\]]

```tree
  Γ(x) = int
  ────────────── (T-Var)   ────────────── (T-Lit)
  Γ ⊢ x : int              Γ ⊢ 1 : int
  ─────────────────────────────────────── (T-Arith)   ─────────────── (T-Lit)
  Γ ⊢ x + 1 : int                                     Γ ⊢ 10 : int
  ──────────────────────────────────────────────────────────────────── (T-Rel)
  Γ ⊢ x + 1 < 10 : bool
```

# §5.3 Commands change the context

```tree
Γ ⊢ e : τ'    τ' ≈ τ    τ has values           Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ
─────────────────────────────────── (T-Decl)   ───────────────────────────────── (T-Assign)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                         Γ ⊢ e₁ = e₂ ⊣ Γ

Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂                     Γ ⊢ c₁ … cₙ ⊣ Γ'
────────────────────────── (T-Seq)             ──────────────────── (T-Block)
Γ ⊢ c cs ⊣ Γ₂                                  Γ ⊢ { c₁ … cₙ } ⊣ Γ
```

* Γ ⊢ c ⊣ Γ', the command is well typed and yields the context for what follows. Declaration extends, sequence threads, block discards.

# §5.3 The checker at work

```lean (name := declMismatch)
#eval (parseProgram "int main() { int x = true; return x; }").map check
```
```leanOutput declMismatch
Except.ok (Except.error (CoreCpp.TypeError.mismatch "initialiser of x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

```lean (name := condInt)
#eval (parseProgram "int main() { return 7 / 2 ? 1 : 0; }").map check
```
```leanOutput condInt
Except.ok (Except.error (CoreCpp.TypeError.mismatch "condition" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

* One function per judgment, the first failing rule names the error. C++ would convert the integer condition, Core C++ has no such conversion.

# §5.4 What a type system buys

* A *type system* is the set of typing rules with their guarantee. In Core C++, every derivation of a well typed program ends in a *value or in `error`*, never stuck.

* `int + bool` has no evaluation rule, the type system rejects it *before* the evaluator meets it.

* `10 / z` has a rule, the one that gives `error`, the type system lets it through, the divisor is a *value*.

* *Static*, before execution, for all executions, what depends on types. *Dynamic*, during execution, what depends on values.

# §5.4 The boundary in Core C++

:::table +header
*
  * Situation
  * Checked
  * By
*
  * `int` added to `bool`
  * statically
  * `T-Arith`
*
  * variable outside its scope
  * statically
  * `T-Var`
*
  * field the class lacks
  * statically
  * `T-Arrow`
*
  * division by zero
  * dynamically
  * `DivZero`
*
  * dereference of `nullptr`
  * dynamically
  * `LocDeref`
*
  * index outside the vector
  * dynamically
  * `LocIndex`
:::

* Python checks everything dynamically. C++ checks types statically but accepts conversions and leaves the dynamic side undefined.

# Summary

* A *type* is a set of values with operations, and the type of a construction is the first part of its meaning.

* Γ ⊢ e : τ types expressions in the context Γ, the static counterpart of ρ. Γ ⊢ c ⊣ Γ' threads the context through commands.

* The rules have the form of the evaluation rules, one per construction, and derivations are trees.

* The type system guarantees *no stuck derivation*. What depends on types is checked statically, what depends on values dynamically.

* Core C++ rejects statically what it can, and gives `error` dynamically where C++ is undefined.

Exercises: see the [lecture notes](../en/Lecture-5___-Values-and-Types/).

```lean -show
end Slides5
```
