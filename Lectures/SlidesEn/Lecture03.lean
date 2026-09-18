/-
Slides of Lecture 3. Each top level section is a slide. Rules and
derivations are preformatted text in `tree` blocks.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Semantics" =>

Judgments, inference rules and the natural semantics of Core C++

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-3___-Semantics/)

{cite}[G. Kahn, *Natural Semantics*, STACS 87, LNCS 247, Springer, 1987.]

```lean -show
namespace Slides3
open CoreCpp
```

# §3.1 Judgments and inference rules

* In natural deduction, a *judgment* is a derivable statement and a *rule* takes premises to a conclusion.

* A *derivation* is a tree of rule applications, with axioms at the leaves.

* Natural semantics uses the same form, with judgments about *programs*.

* Sequent style of Kahn. Context left of ⊢, construction right of it, result after ⇒.

```tree
premise₁    premise₂
──────────────────── (Name)
     conclusion
```

# §3.2 Environment, store and values

* *Environment* ρ, identifiers to *locations* ℓ.

* *Store* σ, locations to *values*. The domain of σ is the set of live locations.

* Values of the current subset. 32 bit `int n` and `bool b`.

* *Reading x is reading σ(ρ(x)). Assigning to x is writing at ρ(x).*

* Two variables may denote the same location, and a location may live after the identifier. References in Unit III, objects in Unit V, *with no rule rewritten*.

# §3.2 The four judgments

:::table +header
*
  * Judgment
  * Reading
*
  * Γ ⊢ e : τ
  * e has type τ in the context Γ
*
  * ρ, σ ⊢ e ⇒ v, σ′
  * under ρ and σ, e evaluates to v and yields σ′
*
  * ρ, σ ⊢ e ⇒ₗ ℓ, σ′
  * under ρ and σ, e denotes the location ℓ
*
  * ρ, σ ⊢ c ⇒ r, ρ′, σ′
  * under ρ and σ, c yields the control r, the environment ρ′ and the store σ′
:::

* The control r is `normal` or `ret v`. Every dynamic judgment admits `error`, which is not a value of the language.

# §3.3 Literals and variables

```tree
─────────────────────────── (Lit)      ──────────────────────── (BoolLit)
ρ, σ ⊢ n ⇒ int32 n, σ                  ρ, σ ⊢ b ⇒ bool b, σ

ρ(x) = ℓ                              ρ, σ ⊢ x ⇒ₗ ℓ, σ    ℓ ∈ dom σ
────────────────────── (LocVar)       ─────────────────────────────── (Var)
ρ, σ ⊢ x ⇒ₗ ℓ, σ                       ρ, σ ⊢ x ⇒ σ(ℓ), σ
```

* `int32` returns the integer when it fits in 32 bits and `error` otherwise.

* The location of a variable must be *live*.

# §3.3 Binary operators

```tree
ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂
──────────────────────────────────────────────── (Arith, ⊕ ∈ {+, −, ×})
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ int32 (n₁ ⊕ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂    n₂ ≠ 0
──────────────────────────────────────────────────────── (Div, ⊘ ∈ {/, %})
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ int32 (n₁ ⊘ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int 0, σ₂
──────────────────────────────────────────────── (DivZero)
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ error
```

* Left before right, the choice of Core C++ where C++17 fixes no order.

# §3.3 Short circuit and a derivation

```tree
ρ, σ ⊢ e₁ ⇒ bool false, σ₁
──────────────────────────────── (And-False)
ρ, σ ⊢ e₁ && e₂ ⇒ bool false, σ₁

ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
─────────────────────────────────────────────── (And-True)
ρ, σ ⊢ e₁ && e₂ ⇒ v, σ₂
```

{exh}[x + 41 with ρ = \[x ↦ ℓ₀\] and σ = \{ℓ₀ ↦ 1\}]

```tree
  ρ(x) = ℓ₀
  ──────────────── (LocVar)
  ρ, σ ⊢ x ⇒ₗ ℓ₀, σ    ℓ₀ ∈ dom σ
  ──────────────────────────────── (Var)    ─────────────────── (Lit)
  ρ, σ ⊢ x ⇒ int 1, σ                       ρ, σ ⊢ 41 ⇒ int 41, σ
  ─────────────────────────────────────────────────────────────── (Arith)
  ρ, σ ⊢ x + 41 ⇒ int 42, σ
```

# §3.4 Declaration and assignment

```tree
ρ, σ ⊢ e ⇒ v, σ′    (ℓ, σ″) = alloc(σ′, v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

* The declaration allocates a *fresh* location and extends ρ. Locations are never reused.

* The assignment evaluates the right side *before* the left one, the order C++17 fixes.

# §3.4 Sequence and block

```tree
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁

ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ′, σ′
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ′ ∖ (ρ′ ∖ ρ)
```

* *Scope* is the restoration of ρ. *Lifetime* is the removal of the locations from σ.

* A `ret` interrupts the sequence and rises to the call.

# §3.4 Loops

```tree
ρ, σ ⊢ e ⇒ bool false, σ₁
──────────────────────────────────────── (While-F)
ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

ρ, σ ⊢ e ⇒ bool true, σ₁   ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂   ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
─────────────────────────────────────────────────────────────────────────────────── (While-T)
ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
────────────────────────────────────────────────────── (While-Ret)
ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂
```

* `While-T` recurs on its *own conclusion*.

# §3.5 The derivation tree printed by the interpreter

```lean (name := traceAssign)
def sum : String :=
  "int main() { int x = 1; x = x + 41; return x; }"

#eval match parseProgram sum with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceAssign
    [], {} ⊢ 1 ⇒ 1, {}   (Lit)
  [], {} ⊢ int x = 1; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Decl)
        [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ 1, {ℓ0 ↦ 1}   (Var)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ 41 ⇒ 41, {ℓ0 ↦ 1}   (Lit)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x + 41 ⇒ 42, {ℓ0 ↦ 1}   (Binary)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x = x + 41; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 42}   (Assign)
      [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 42}   (LocVar)
    [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ x ⇒ 42, {ℓ0 ↦ 42}   (Var)
  [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ return x; ⇒ ret 42, [x ↦ ℓ0], {ℓ0 ↦ 42}   (Return)
[], {} ⊢ main() ⇒ 42, {ℓ0 ↦ 42}   (Call)
```

* *Post order*, premises before the conclusion, indented by depth. The root is the last line.

# §3.6 Error, determinism and divergence

```lean (name := divZero)
#eval (parseProgram "int main() { return 10 / 0; }").map run
```
```leanOutput divZero
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

* *Progress*. Every derivation of a well typed program ends in a value or in `error`.

* *Determinism*. Mutually exclusive premises, at most one derivation. In C++, `f() + g()` may have two results.

* *Divergence*. `while (true) { }` has no finite derivation. The inductive semantics does not describe programs that do not terminate.

{cite}[X. Leroy and H. Grall, *Coinductive big-step operational semantics*, Information and Computation 207(2), 2009.]

# §3.7 Static semantics

```tree
Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)
Γ ⊢ e₁ ⊕ e₂ : int
```

```lean (name := typeError)
def sumBool : String := "int main() { return 1 + true; }"

#eval (parseProgram sumBool).map check
```
```leanOutput typeError
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

* Same form as the evaluation rules, *without a store*, checked before execution. Unit II treats types.

# Summary

* A *judgment* states what a construction computes in a context, and a *derivation* is a tree of rules.

* *Environment* ρ maps identifiers to locations, *store* σ maps locations to values. Reading x is reading σ(ρ(x)).

* Expressions evaluate left to right, with short circuit in `&&` and `||`, and division by zero is `error`.

* Declaration allocates, assignment writes, block restores ρ and removes locations from σ, `while` recurs on its own conclusion.

* The interpreter prints the *derivation tree* in post order, and the semantics does not describe diverging programs.

Exercises: see the [lecture notes](../en/Lecture-3___-Semantics/).

```lean -show
end Slides3
```
