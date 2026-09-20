/-
Slides of Lecture 8. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Expressions" =>

Evaluation order, short circuit, the conditional and the fragment in Lean

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-8___-Expressions/)

```lean -show
namespace Slides8
open CoreCpp
```

# §8.1 Expressions and commands

* An *expression* is evaluated to a value. A *command* is executed for its effect and has no value.

* Two nonterminals, `Expr` and `Cmd`, two judgments, ρ, σ ⊢ e ⇒ v, σ′ and ρ, σ ⊢ c ⇒ r, ρ′, σ′.

* Assignment is a *command*. `x = y = 1` is not Core C++. An expression becomes a command only with the semicolon.

* C++ makes assignment an expression. Core C++ separates them so that *an expression has an effect only through a call*, and a call only through the pointers it receives.

# §8.2 Evaluation order matters

```lean (name := ordem)
def ordem : String :=
  "class Cont { public: int n; };
  int prox(Cont* c) {
    c->n = c->n + 1;
    return c->n;
  }
  int main() {
    Cont* c = new Cont();
    return prox(c) + 10 * prox(c);
  }"

#eval (parseProgram ordem).map run
```
```leanOutput ordem
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* Left first, 1 + 10 · 2. `Arith` threads σ into the left operand and σ₁ into the right one.

* C++17 leaves the order of `+` *unspecified*, a compiler may compute 21 or 12. Core C++ has *one derivation and one result*.

# §8.2 The orders of the fragment

:::table +header
*
  * Construction
  * Core C++
  * C++17
*
  * `e₁ ⊕ e₂`, `e₁ ⋈ e₂`
  * left, then right
  * unspecified
*
  * `e₁ = e₂`
  * right, then left
  * fixed, the same
*
  * `e[i]`
  * vector, then index
  * fixed, the same
*
  * `f(e₁, …, eₖ)`
  * arguments left to right
  * unspecified
*
  * `e₁ && e₂`, `e₁ || e₂`
  * left, then right if needed
  * fixed, the same
*
  * `e₁ ? e₂ : e₃`
  * condition, then one branch
  * fixed, the same
:::

# §8.3 Short circuit

```lean (name := shortAnd)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z != 0 && 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortAnd
Except.ok (Except.ok (CoreCpp.Val.int 0))
```

```lean (name := shortOr)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z == 0 || 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortOr
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* `And-False` and `Or-True` have *no premise* about the second operand. The division by zero never runs.

# §8.3 The skipped operand in the derivation

```lean (name := traceShort)
#eval match parseProgram "int main() { int z = 0; bool b = z != 0 && 10 / z > 1; return b ? 1 : 0; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceShort
    [], {} ⊢ 0 ⇒ 0, {}   (Lit)
  [], {} ⊢ int z = 0; ⇒ normal, [z ↦ ℓ0], {ℓ0 ↦ 0}   (Decl)
          [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z ⇒ₗ ℓ0, {ℓ0 ↦ 0}   (LocVar)
        [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z ⇒ 0, {ℓ0 ↦ 0}   (Var)
        [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ 0 ⇒ 0, {ℓ0 ↦ 0}   (Lit)
      [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z != 0 ⇒ false, {ℓ0 ↦ 0}   (Binary)
    [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z != 0 && 10 / z > 1 ⇒ false, {ℓ0 ↦ 0}   (And)
  [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ bool b = z != 0 && 10 / z > 1; ⇒ normal, [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false}   (Decl)
        [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ⇒ₗ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ false}   (LocVar)
      [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ⇒ false, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Var)
      [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ 0 ⇒ 0, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Lit)
    [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ? 1 : 0 ⇒ 0, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Cond)
  [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ return b ? 1 : 0; ⇒ ret 0, [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false}   (Return)
[], {} ⊢ main() ⇒ 0, {}   (Call)
```

* Under `And` there is one child, no derivation of the division.

# §8.4 The conditional expression

```lean (name := condSkip)
#eval (parseProgram "int main() { int z = 0; return z == 0 ? 42 : 10 / z; }").map run
```
```leanOutput condSkip
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* The expression counterpart of `if`. Condition, then *exactly one branch*, `Cond-T` or `Cond-F`.

* The branches have *one type*, `T-Cond`, because the expression has one type whatever the run time decides.

* It is what makes `soma` over a list a single expression.

# §8.5 Arithmetic details

```lean (name := truncation)
#eval (parseProgram "int main() { return -7 / 2 * 10 + -7 % 2; }").map run
```
```leanOutput truncation
Except.ok (Except.ok (CoreCpp.Val.int (-31)))
```

* Division and remainder *truncate toward zero*, as C++ fixes. `-7 / 2` is `-3`, `-7 % 2` is `-1`, and `(a / b) * b + a % b = a`.

* Every result passes through `int32`. Outside 32 bits, `error`, where C++ is undefined. *This is what makes `int` a 32 bit type in the semantics.*

# §8.6 The fragment in Lean

:::table +header
*
  * Construction
  * Typing
  * Evaluation
  * Lean
*
  * literals, variables, operators, conditional
  * `T-Lit` to `T-Cond`
  * `Lit` to `Cond`
  * `Typing.expr`, `Eval.expr`
*
  * `nullptr`, `new C()`, `new std::vector<τ>(n)`
  * `T-Null`, `T-New`, `T-NewVec`
  * `Null`, `New`, `NewVec`
  * `Typing.expr`, `Eval.expr`
*
  * `*e`, `e.f`, `e->f`, `e[i]`
  * `T-Loc…`
  * `Loc…`, `Read`
  * `Typing.lval`, `Eval.lval`
*
  * declaration, assignment, block, loops, `return`
  * `T-Decl` to `T-Ret`
  * `Decl` to `Return`
  * `Typing.cmd`, `Eval.cmd`
*
  * call, function, class, program
  * `T-Call`, `T-Fun`, `T-Class`, `T-Program`
  * `Call`, `Program`
  * `Typing.fn`, `check`, `runWith`
:::

* Every rule stands in the comment of its case, and the [blueprint](https://christianobraga.github.io/corecpp/) links each rule to its code.

# Summary

* *Expressions* have values, *commands* have effects. Assignment is a command in Core C++.

* Once expressions call functions with effects, *evaluation order is part of the meaning*. Core C++ fixes left to right where C++17 does not.

* `&&`, `||` and `?:` *skip* an operand, and a skipped operand may be one that would be `error`.

* Division truncates toward zero and every result passes through `int32`.

* The fragment at the end of Unit II. Basic types, classes with fields, pointers, vectors, commands and first order functions, *no rule rewritten* by the units to come.

Exercises: see the [lecture notes](../en/Lecture-8___-Expressions/).

```lean -show
end Slides8
```
