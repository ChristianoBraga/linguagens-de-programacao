/-
Slides of Lecture 11. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Commands and Control" =>

Sequence, block, selection, repetition and the control result

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-11___-Commands-and-Control/)

```lean -show
namespace Slides11
open CoreCpp
```

# §11.1 Sequence and the control result

```tree
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁
```

* Environment and store flow from each command to the next.

* The *control result* r is `normal` or `ret v`. Not a value of the language, no expression observes it.

* It gives `return` a meaning *without a jump*.

# §11.2 Block

```tree
ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ', σ'
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ' ∖ (ρ' ∖ ρ)
```

* The control *passes through*, a `return` in a block returns from the function.

* ρ is *restored*, the names of the block are not visible after it. Scope.

* σ loses the *owned* locations of ρ' ∖ ρ, the variables of the block cease to exist. Lifetime.

* Every branch, every loop body, every function body is a block. Scope is always delimited by braces.

# §11.3 Selection

```tree
ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c₁} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-T)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂

ρ, σ ⊢ e ⇒ bool false, σ₁    ρ, σ₁ ⊢ {c₂} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-F)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂
```

* The branch starts from the store the condition produced.

* `if` without `else` has an empty second block. The condition is `bool`, an `int` condition is a type error.

# §11.3 The derivation of a selection

```lean (name := ifRun)
def halve : String :=
  "int main() {
     int x = 2;
     if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
     return x;
   }"

#eval (parseProgram halve).map run
```
```leanOutput ifRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x % 2 == 0 ⇒ true, {ℓ0 ↦ 2}   (Binary)
      ...
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ { x = x / 2; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
  [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ if (x % 2 == 0) { x = x / 2; } else { x = x - 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (If)
```

* The chosen block appears, the other does not.

# §11.4 Repetition

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

* n iterations nest n applications of `While-T` and one of `While-F`. A loop that never ends has *no derivation*.

# §11.4 A return inside a loop

```lean (name := whileRet)
def untilSeven : String :=
  "int main() {
     int i = 0;
     while (true) {
       i = i + 1;
       if (i == 7) { return i; }
     }
   }"

#eval (parseProgram untilSeven).map run
```
```leanOutput whileRet
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

* `Return` produces `ret 7`, `If-T` passes it, `Seq-Ret` stops the body, `While-Ret` stops the loop, `Call` consumes it. Four rules, no jump.

# §11.4 The for loop

```tree
ρ, σ ⊢ c₀ ⇒ normal, ρ₀, σ₀    ρ₀, σ₀ ⊢ while (e) { {c} cₛ } ⇒ r, ρ₀, σ₁
────────────────────────────────────────────────────────────────────── (For)
ρ, σ ⊢ for (c₀; e; cₛ) {c} ⇒ r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)
```

* Defined through `while`. The initialiser runs once, its variable has the loop as scope.

* The body is its own block, the step runs after it, outside the body's scope.

* The conclusion frees the loop variable, with the ownership reading of `Block`.

# §11.5 Control without jumps

* No `break`, `continue`, `goto`, exceptions. Out of a loop by its condition or by `return`.

* Each missing construction is a *non local transfer of control*, and needs a new control result or continuations.

* `break` as an exercise. A result `brk`, passed by `If` and `Seq-Ret`, consumed by `While` as `normal`, rejected by the type checker outside a loop.

* First place where the type checker must know *in which construction* a command occurs.

# Summary

* *Sequence* threads ρ and σ, and a `ret` stops it. The *control result* replaces jumps.

* *Block* passes the control, restores ρ and frees the owned locations. Scope and lifetime.

* *Selection* runs one block from the store the condition produced.

* *Repetition* has three rules, and `While-T` recurs on its own conclusion. `for` is `while` with a block.

* A `return` inside a loop is handled by four rules and no jump.

Exercises: see the [lecture notes](../en/Lecture-11___-Commands-and-Control/).

```lean -show
end Slides11
```
