import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Meta.Footnote
import Lectures.Papers
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lecture 8: Expressions" =>

%%%
tag := "lecture-8"
%%%

```lean -show
namespace Lecture8
open CoreCpp
```

This lecture closes Unit II with the expressions as a whole. It states what an expression is and what distinguishes it from a command, fixes the evaluation order and shows why the order is part of the meaning once expressions have effects, presents the two constructions that skip the evaluation of an operand, short circuit and the conditional, and reviews the whole fragment of Core C++ implemented so far as it stands in the Lean interpreter.

*This lecture is also available as [presentation slides](../slides/lecture-8.en.html).*

# Expressions and Commands

%%%
tag := "expressions-commands"
%%%

An *expression* is a construction that is evaluated to a value. A *command* is a construction that is executed for its effect on the store and has no value. Core C++ keeps the two apart in the grammar, `Expr` and `Cmd`, and in the judgments, ρ, σ ⊢ e ⇒ v, σ′ for expressions and ρ, σ ⊢ c ⇒ r, ρ′, σ′ for commands. Assignment is a command, so `x = y = 1` is not a Core C++ program, and an expression becomes a command only when followed by a semicolon, the expression statement that discards its value.

The separation is a decision of the language design, and C++ takes the other one, in which assignment is an expression with a value, and `while ((c = read()) != 0)` is idiomatic. Core C++ prefers the separation because it keeps the expressions of Unit I free of effects, and because it makes the effects of this unit, the ones a function call performs on the store, easier to locate. An expression has an effect only through a call, and a call has an effect only through the pointers it receives.

# Evaluation Order

%%%
tag := "order"
%%%

When an expression has no effect on the store, the order in which its operands are evaluated does not change its value, and the rules of {secref}[lecture-3] could evaluate them in any order. When a call inside an expression writes through a pointer, the order matters. The program below calls `next` twice on the same counter, and the value of the sum depends on which call runs first.

```lean (name := ordem)
def ordem : String :=
  "class Cell { public: int n; };
  int next(Cell* c) {
    c->n = c->n + 1;
    return c->n;
  }
  int main() {
    Cell* c = new Cell();
    return next(c) + 10 * next(c);
  }"

#eval (parseProgram ordem).map run
```
```leanOutput ordem
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

Core C++ evaluates the left operand first, so the first call returns 1 and the second returns 2, and the sum is 1 + 20. The rule `Arith` fixes that order by threading the store, σ into the left operand, σ₁ out of it and into the right one. C++17 leaves the order of the operands of `+` unspecified, so a C++ compiler may compute 21 or 12 for the same program, and both are correct C++. This is the case the course chose in Unit I to show what determinism means. Core C++ has one derivation and one result, and C++ has a set of admitted results, of which Core C++ picks one.

The orders C++17 does fix, Core C++ keeps. The right side of an assignment is evaluated before the left side, the vector before the index in `v[i]`, and the function before its arguments in a call. {numref}[tbl-order] lists the orders of the fragment.

:::table +header
*
  * Construction
  * Order in Core C++
  * In C++17
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

{tabcap "tbl-order"}[Evaluation order in Core C++ and what C++17 fixes.]

# Short Circuit

%%%
tag := "short-circuit"
%%%

The conjunction and the disjunction evaluate their second operand only when the first does not decide the result. The rules of {secref}[lecture-3] express it with two rules per operator, and the consequence is that the second operand may contain an expression that would be `error` if evaluated.

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

The division by zero never runs, because `z != 0` is false and `And-False` has no premise about the second operand. The disjunction behaves symmetrically, and `Or-True` skips the second operand when the first is true.

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

The derivation tree shows the skipped operand as an absent branch. Under the `And` node there is one child, the derivation of `z != 0`, and no derivation of the division.

```lean (name := traceShort)
#eval match parseProgram "int main() { int z = 0; bool b = z != 0 && 10 / z > 1; return b ? 1 : 0; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceShort
ρ₀ = []                    σ₀ = {}
ρ₁ = [z ↦ ℓ0]              σ₁ = {ℓ0 ↦ 0}
ρ₂ = [z ↦ ℓ0, b ↦ ℓ1]      σ₂ = {ℓ0 ↦ 0, ℓ1 ↦ false}

                   𝒟₁                                                𝒟₂                                                   𝒟₃
  ρ₀, σ₀ ⊢ int z = 0; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ bool b = z != 0 && 10 / z > 1; ⇒ normal, ρ₂, σ₂    ρ₂, σ₂ ⊢ return b ? 1 : 0; ⇒ ret 0, ρ₂, σ₂
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 0, σ₀

𝒟₁
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 0 ⇒ 0, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int z = 0; ⇒ normal, ρ₁, σ₁

𝒟₂
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ z ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)    ────────────────── (Lit)
  ρ₁, σ₁ ⊢ z ⇒ 0, σ₁                     ρ₁, σ₁ ⊢ 0 ⇒ 0, σ₁
  ─────────────────────────────────────────────────────────────── (Binary)
  ρ₁, σ₁ ⊢ z != 0 ⇒ false, σ₁
  ──────────────────────────────────────────────────────────────────────── (And)
  ρ₁, σ₁ ⊢ z != 0 && 10 / z > 1 ⇒ false, σ₁
  ────────────────────────────────────────────────────────────────────────────── (Decl)
  ρ₁, σ₁ ⊢ bool b = z != 0 && 10 / z > 1; ⇒ normal, ρ₂, σ₂

𝒟₃
  ──────────────────── (LocVar)
  ρ₂, σ₂ ⊢ b ⇒ₗ ℓ1, σ₂
  ───────────────────────────── (Var)    ────────────────── (Lit)
  ρ₂, σ₂ ⊢ b ⇒ false, σ₂                 ρ₂, σ₂ ⊢ 0 ⇒ 0, σ₂
  ─────────────────────────────────────────────────────────────── (Cond)
  ρ₂, σ₂ ⊢ b ? 1 : 0 ⇒ 0, σ₂
  ────────────────────────────────────────────────────────────────────── (Return)
  ρ₂, σ₂ ⊢ return b ? 1 : 0; ⇒ ret 0, ρ₂, σ₂
```

# The Conditional Expression

%%%
tag := "conditional"
%%%

The conditional `e₁ ? e₂ : e₃` is the expression counterpart of the `if` command. It evaluates the condition and then exactly one branch, by the rules `Cond-T` and `Cond-F`, so a branch that would be `error` is harmless when not chosen. The types of the two branches must agree, by `T-Cond`, because the expression has one type whatever the condition decides at run time.

```lean (name := condSkip)
#eval (parseProgram "int main() { int z = 0; return z == 0 ? 42 : 10 / z; }").map run
```
```leanOutput condSkip
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The conditional is what makes recursion over a recursive type possible in a single expression, as `sum` in {secref}[lecture-7] shows. Without it, the base case would need an `if` command and two `return` commands.

# Arithmetic Details

%%%
tag := "arithmetic"
%%%

Two details of the arithmetic of `int` are part of the meaning of the expressions. Division and remainder truncate toward zero, as C++ fixes, so `-7 / 2` is `-3` and `-7 % 2` is `-1`, and the identity `(a / b) * b + a % b = a` holds for negative operands too.

```lean (name := truncation)
#eval (parseProgram "int main() { return -7 / 2 * 10 + -7 % 2; }").map run
```
```leanOutput truncation
Except.ok (Except.ok (CoreCpp.Val.int (-31)))
```

Every arithmetic result passes through `int32`, and a result outside 32 bits is `error`, where C++ leaves the signed overflow undefined. The check is dynamic, because the operands are values, and it is the rule that makes `int` a type of 32 bit integers in the semantics and not a type of unbounded integers with a name borrowed from C++.

# The Fragment in Lean

%%%
tag := "fragment"
%%%

The fragment of Core C++ implemented at the end of Unit II has the basic types, the classes with fields, the pointers, the vectors, the expressions of this unit, the commands of Unit I and first order functions. {numref}[tbl-fragment] lists the constructions and the Lean functions that give them their meaning.

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
  * declaration, assignment, block, `if`, `while`, `for`, `return`
  * `T-Decl` to `T-Ret`
  * `Decl` to `Return`
  * `Typing.cmd`, `Eval.cmd`
*
  * call, function, class, program
  * `T-Call`, `T-Fun`, `T-Class`, `T-Program`
  * `Call`, `Program`
  * `Typing.fn`, `check`, `runWith`
:::

{tabcap "tbl-fragment"}[The fragment of Core C++ at the end of Unit II and its implementation.]

Each rule stands in the comment of the case that implements it, and the [blueprint](https://christianobraga.github.io/corecpp/) presents every rule with a link to its code. The next units add constructions to this fragment, references in Unit III, functions as values in Unit IV, methods and destructors in Unit V, templates and overloading in Unit VI, and no rule of this unit is rewritten by any of them.

# Exercises

%%%
tag := "exercises-8"
%%%

{exercise "exr-order-result"}[] Predict the value of `next(c) * 10 + next(c) - next(c)` after `Cell* c = new Cell();`, with `next` as in {secref}[order], and then the two other values a C++ compiler may compute for it.

{exercise "exr-short-circuit-rules"}[] Write the two rules of `||` in the notation of the course, and build the derivation of `z == 0 || 10 / z > 1` in a store where `z` is 0.

{exercise "exr-assignment-expression"}[] Suppose assignment were an expression whose value is the assigned value, as in C++. Write its typing and evaluation rules, and say which programs would then type that Core C++ rejects today.

{exercise "exr-cond-versus-if"}[] Rewrite `sum` of {secref}[lecture-7] with an `if` command and two `return` commands, and compare the two derivation trees for a list of one node.

{exercise "exr-truncation"}[] Compute `a / b` and `a % b` for the four sign combinations of `a = 7` and `b = 2`, by the rules of Core C++, and check the identity `(a / b) * b + a % b = a` in each case.

{exercise "exr-fragment-extension"}[] Choose a construction of C++ that the fragment lacks, other than the ones the next units announce, write its typing and evaluation rules, and say whether it could be added without rewriting a rule of this unit.

```lean -show
end Lecture8
```
