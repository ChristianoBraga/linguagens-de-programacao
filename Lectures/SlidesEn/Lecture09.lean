/-
Slides of Lecture 9. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Variables and Storage" =>

The six attributes of a variable, declaration, assignment and block exit

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-9___-Variables-and-Storage/)

```lean -show
namespace Slides9
open CoreCpp
```

# §9.1 Two maps instead of one

* A map from names to values cannot express two names for one variable, a name that outlives a block, an object several pointers reach.

* The *location* is the level in between. ρ maps identifiers to locations, σ maps locations to values.

* *A variable is a pair*, a binding in ρ and a location in σ. Reading x is σ(ρ(x)), assigning to x writes at ρ(x).

* Declaration extends ρ and allocates in σ. Assignment changes σ only. Block exit restores ρ and shrinks σ.

* The *storables*, what a location may hold, are `int`, `bool` and pointers. An object is a record of locations, never a storable.

# §9.2 The six attributes

:::table +header
*
  * Attribute
  * Where
  * Fixed by
*
  * identifier
  * key in ρ and Γ
  * declaration
*
  * location
  * ρ(x)
  * declaration, alloc
*
  * value
  * σ(ρ(x))
  * initialiser, then assignments
*
  * type
  * Γ(x)
  * declaration, static
*
  * scope
  * commands with x in ρ
  * the declaring block
*
  * lifetime
  * ρ(x) in dom σ
  * alloc to block exit
:::

* Identifier, type and scope are *static*. Location, value and lifetime are *dynamic*, they exist only in a derivation.

# §9.3 Declaration

```tree
Γ ⊢ e : τ'    τ' ≈ τ    τ has values
─────────────────────────────────────── (T-Decl)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ v, σ'    (ℓ, σ″) = alloc(σ', v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

* alloc returns a location outside dom σ. *Locations are never reused.*

* The output environment carries the binding to the following commands.

```lean (name := noInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput noInit
Except.error "syntax error at token 7 (';'): expected '='"
```

# §9.4 Assignment

```tree
Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ    τ has values
───────────────────────────────────────────────────── (T-Assign)
Γ ⊢ e₁ = e₂ ⊣ Γ

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

* Right side first, then the location of the left side, the order C++17 fixes.

* The type of a variable never changes.

```lean (name := assignBool)
#eval (parseProgram "int main() { int x = 1; x = true; return x; }").map check
```
```leanOutput assignBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "assignment to x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

# §9.5 Shadowing

```lean (name := shadowRun)
def shadow : String :=
  "int main() {
     int x = 1;
     { int x = 10; x = x + 1; }
     return x;
   }"

#eval (parseProgram shadow).map run
```
```leanOutput shadowRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* The inner binding enters at the front of ρ and lookup finds it first. Two variables, two locations.

* At the closing brace the inner binding leaves ρ and ℓ1 leaves σ.

# §9.5 The derivation of a block

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int x = 10; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Decl)
      ...
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
    [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x = x + 1; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 11}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int x = 10; x = x + 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
```

* `Block` returns the outer ρ and a store without ℓ1. Any later access to ℓ1 would be `error`.

* C++ releases the storage too, and leaves a later access *undefined*.

# Summary

* A variable is a *binding in ρ* and a *location in σ*. Reading is σ(ρ(x)), assigning writes at ρ(x).

* Six attributes, three static, identifier, type and scope, three dynamic, location, value and lifetime.

* *Declaration* allocates and extends ρ. *Assignment* writes at a live location, right side first.

* *Shadowing* is a second binding for one name, with its own location. Block exit removes both.

* Locations are never reused, and an access to a freed location is `error`, not undefined.

Exercises: see the [lecture notes](../en/Lecture-9___-Variables-and-Storage/).

```lean -show
end Slides9
```
