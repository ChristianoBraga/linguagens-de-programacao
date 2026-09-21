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

#doc (Manual) "Lecture 12: Expressions with Side Effects" =>

%%%
tag := "lecture-12"
%%%

```lean -show
namespace Lecture12
open CoreCpp
```

This lecture closes Unit III with the interaction between expressions and the store. An expression has a *side effect* when its evaluation changes the store, and in Core C++ that happens only through a function call. The lecture shows why the order of evaluation becomes part of the meaning once effects exist, states the orders Core C++ fixes, contrasts them with what C++17 leaves to the compiler, and reviews the whole fragment of the language implemented up to this unit.

*This lecture is also available as [presentation slides](../slides/lecture-12.en.html).*

# Effects Through Calls

%%%
tag := "effects"
%%%

An expression of Unit I has no effect. Its rules thread the store through the premises, ρ, σ ⊢ e ⇒ v, σ', but every rule returns the store it received, and the order of the operands does not matter for the value. {secref}[lecture-8] showed the first expression with an effect, a call to a function that writes through a pointer. The function `next` below increments a counter reached through its parameter and returns the new value.

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

The two calls return different values, 1 and 2, because the store changes between them. The sum is 1 + 10 · 2 = 21 when the left call runs first, and 2 + 10 · 1 = 12 when the right one does. The value of the expression depends on the order of evaluation, and the order is therefore part of the meaning of `+`.

# The Orders Core C++ Fixes

%%%
tag := "orders"
%%%

Core C++ fixes one order for every construction, and the rules carry it in the order of their premises. {numref}[tbl-orders] lists them.

:::table +header
*
  * Construction
  * Order
  * Rule
  * In C++17
*
  * `e₁ ⊕ e₂`
  * left operand, then right
  * `Binary`
  * unspecified
*
  * `f(e₁, …, eₖ)`
  * arguments left to right
  * `Call`
  * unspecified
*
  * `e₁ = e₂`
  * right side, then left
  * `Assign`
  * right before left
*
  * `e[i]`
  * vector, then index
  * `LocIndex`
  * object before index
*
  * `e₁ && e₂`, `e₁ || e₂`
  * left, then right only if needed
  * `And`, `Or`
  * the same
*
  * `e₁ ? e₂ : e₃`
  * condition, then the chosen branch
  * `Cond`
  * the same
:::

{tabcap "tbl-orders"}[The evaluation orders of Core C++ and their status in C++17.]

The first two lines are decisions of Core C++ where C++17 makes none. The standard says that the operands of `+` and the arguments of a call are evaluated in an unspecified order, and a compiler may choose any order, and even a different one at each occurrence. The last four lines are orders C++17 fixes, and Core C++ keeps them. The assignment evaluates its right side first since C++17, a change from earlier standards made to remove a class of unspecified results.

The rule `Binary` is the one that carries the first decision. Its premises read ρ, σ ⊢ e₁ ⇒ v₁, σ₁ and then ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂. The second premise starts from the store the first produced, and the order of the premises is the order of evaluation.

```
ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

# The Alternative Derivation

%%%
tag := "alternative"
%%%

A C++ compiler that evaluates the right operand first applies a rule Core C++ does not have.

```
ρ, σ ⊢ e₂ ⇒ v₂, σ₁    ρ, σ₁ ⊢ e₁ ⇒ v₁, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary-RL)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

Under `Binary-RL` the program of {secref}[effects] returns 12. Both derivations are valid for C++17, and the standard does not choose. A language whose semantics has both rules is *nondeterministic*, a program may have two results, and a correct program must produce the same result under both, which is a proof obligation the standard leaves to the programmer.

Core C++ has one rule and one result, the property {secref}[lecture-3] called determinism. The price is a difference from C++ that the course states once. A Core C++ program with two effectful calls in one expression has the value Core C++ gives it, and a C++ compiler may give it another. The example `call_order.cpp` of the repository returns 21 under the interpreter, and returns 21 or 12 under `g++`, according to the version and the options.

The assignment shows the fixed order at work. The right side is evaluated first, so `next(c)` returns 1 there, and the index on the left side is evaluated afterwards and returns 2.

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

The element at index 2 receives 1, the element at index 1 keeps its default 0, and the result is 0 · 10 + 1. Under the order of C++14 and earlier the same program could store 2 at index 1.

The arguments of a call follow the same discipline. The first argument is evaluated first, and the second sees the store the first left.

```lean (name := callOrder)
def callOrder : String :=
  "class Cell { public: int n; };
   int next(Cell* c) { c->n = c->n + 1; return c->n; }
   int f(int a, int b) { return a * 10 + b; }
   int main() {
     Cell* c = new Cell();
     return f(next(c), next(c));
   }"

#eval (parseProgram callOrder).map run
```
```leanOutput callOrder
Except.ok (Except.ok (CoreCpp.Val.int 12))
```

# Why Not Forbid Effects in Expressions

%%%
tag := "why-not"
%%%

A language may avoid the whole question by forbidding calls with effects inside expressions, or by forbidding effects altogether, as a pure functional language does. Core C++ keeps them for two reasons. The first is fidelity to C++, where a call in an expression is ordinary. The second is that the rules already have everything they need. The store was threaded through the expression judgment from {secref}[lecture-3], precisely so that a call inside an expression could change it, and no rule of this unit was rewritten to admit effects. The decision of {secref}[lecture-3] to write ρ, σ ⊢ e ⇒ v, σ' and not ρ, σ ⊢ e ⇒ v pays off here.

What the rules do fix is the order, and that is the lesson of the unit. A side effect is not a flaw of the semantics, it is a feature of the language that the semantics has to describe completely, and describing it completely means choosing an order where the language leaves it open.

# The Fragment So Far

%%%
tag := "fragment-12"
%%%

Three units have built the following fragment of Core C++, all of it in the interpreter and in the [blueprint](https://christianobraga.github.io/corecpp/) of the language. Types `int`, `bool`, `void`, classes with fields, pointers to classes and to vectors, and `std::vector<τ>`. Expressions with literals, variables, the arithmetic, relational and logical operators, the conditional, `new`, field access, dereference, indexing and calls. Commands with declaration, reference declaration, assignment, block, `if`, `while`, `for` and `return`. Functions with call by value. Twenty three example programs, each compiling with `g++` to the exit code the interpreter computes, or to an undefined result where Core C++ gives `error`.

Unit IV adds the constructions of abstraction. Parameters by reference, which reuse the rule `DeclRef` at the call. Lambdas and `std::function`, which make a function a value with an environment of its own. And the comparison of call by value, by reference and by name, the last one with Haskell as the language of contrast.

# Exercises

%%%
tag := "exercises-12"
%%%

{exercise "exr-both-orders"}[] For the program of {secref}[effects], build the two derivations, one with `Binary` and one with `Binary-RL`, up to the sum, and show where the stores differ.

{exercise "exr-order-independent"}[] Give a condition on the functions called in `f(x) + g(y)` under which the two orders produce the same value and the same final store, and argue from the rules that the condition suffices.

{exercise "exr-assign-old-order"}[] Write the assignment rule of C++14, in which the order of the two sides is unspecified, as two rules, and give a Core C++ program that produces two different final stores under them.

{exercise "exr-call-arguments"}[] Write the rule `Call-RL` that evaluates the arguments right to left and compute, under it, the result of the program of {secref}[alternative] that calls `f(next(c), next(c))`.

{exercise "exr-pure-fragment"}[] Identify the largest subset of the expressions of Core C++ in which the order of evaluation is irrelevant, and prove, by induction on the rules, that in it ρ, σ ⊢ e ⇒ v, σ' implies σ' = σ.

{exercise "exr-count-effects"}[] Write a Core C++ program in which one expression contains three calls with effects, predict its value from the rules, and check it with the interpreter and with `g++`. Report whether `g++` agreed and explain why either outcome is consistent with C++17.

```lean -show
end Lecture12
```
