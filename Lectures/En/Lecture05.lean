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

#doc (Manual) "Lecture 5: Values and Types" =>

%%%
tag := "lecture-5"
%%%

```lean -show
namespace Lecture5
open CoreCpp
```

This lecture opens Unit II, on types. It defines values and types, presents the typing judgment Γ ⊢ e : τ and the context Γ, writes the typing rules of the expressions already in Core C++, and states what a type system buys, which errors it rejects before execution and which it leaves to run time. The thread of the unit is the meaning of each construction, and a type is the first part of that meaning, the set of values the construction may produce.

*This lecture is also available as [presentation slides](../slides/lecture-5.en.html).*

# Values and Types

%%%
tag := "values-types"
%%%

A *value* is a datum a program computes, stores, passes to a function or returns from one. In Core C++ the values of Unit I are the 32 bit integers and the two booleans, and this unit adds pointers and the objects they reach. A *type* is a set of values together with the operations that apply to them. The type `int` is the set of integers between $`-2^{31}` and $`2^{31}-1` with the arithmetic and relational operators, and the type `bool` is the set of the two truth values with negation, conjunction and disjunction.

Types classify values, and the classification serves two purposes. It tells the processor how much memory a value takes and how its bits are read, and it tells the programmer which operations make sense on a value. The second purpose is the one this unit develops. An operation applied to a value outside its type has no meaning, and a language decides what to do with such a program, reject it before execution, stop it during execution, or let the machine do whatever the bits say.

Watt divides types into *primitive* types, whose values are atomic, and *composite* types, whose values are built from other values.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, chapter 2.] The primitive types of Core C++ are `int` and `bool`. The composite types are the classes and the vectors of this unit, and the *recursive* types are the classes whose fields point to objects of the same class, such as the nodes of a list. {numref}[tbl-types] summarises the types of the unit and where they appear.

:::table +header
*
  * Kind
  * Types
  * Values
  * Lecture
*
  * primitive
  * `int`, `bool`
  * integers of 32 bits, `true` and `false`
  * this one
*
  * composite
  * `class C` with fields
  * records of locations, reached through `C*`
  * {secref}[lecture-6]
*
  * recursive
  * `class Node` with a field `Node*`
  * finite chains of records
  * {secref}[lecture-7]
*
  * composite
  * `std::vector<int>`
  * sequences of locations, reached through a pointer
  * {secref}[lecture-7]
:::

{tabcap "tbl-types"}[The types of Unit II.]

# The Typing Judgment

%%%
tag := "typing-judgment"
%%%

The *typing judgment* Γ ⊢ e : τ states that the expression e has type τ in the *typing context* Γ, a finite map from identifiers to types. The context plays, for types, the role the environment ρ plays for locations. When a declaration `int x = 1` is checked, x enters Γ with type `int`, and every later use of x reads that type from Γ. The typing context is the static counterpart of the environment, and it never mentions the store, because types are decided before any value exists.

The rules of the judgment have the same form as the evaluation rules of Unit I. A literal has its own type, a variable has the type Γ gives it, and an operator has a rule that fixes the types of the operands and the type of the result.

```
─────────────── (T-Lit)      ─────────────── (T-BoolLit)      Γ(x) = τ
Γ ⊢ n : int                  Γ ⊢ b : bool                     ─────────── (T-Var)
                                                              Γ ⊢ x : τ

Γ ⊢ e₁ : int    Γ ⊢ e₂ : int                Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)      ──────────────────────────── (T-Rel)
Γ ⊢ e₁ ⊕ e₂ : int                           Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : bool              Γ ⊢ e : bool             Γ ⊢ e : int
────────────────────────────── (T-Logic)    ────────────── (T-Not)   ────────────── (T-Neg)
Γ ⊢ e₁ ⊙ e₂ : bool                          Γ ⊢ !e : bool            Γ ⊢ -e : int
```

The arithmetic operators, ⊕, are `+`, `-`, `*`, `/` and `%`, the relational ones, ⋈, are `<`, `<=`, `>` and `>=`, and the logical ones, ⊙, are `&&` and `||`. Equality has a rule of its own, because it compares values of any type with values, `int` with `int`, `bool` with `bool`, and, from {secref}[lecture-7] on, pointers with pointers.

```
Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    τ₁ ≈ τ₂    τ₁, τ₂ have values
──────────────────────────────────────────────────────── (T-Eq, ⋈ ∈ {==, !=})
Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ has values
─────────────────────────────────────────────────────── (T-Cond)
Γ ⊢ e₁ ? e₂ : e₃ : τ
```

The relation τ₁ ≈ τ₂ is equality of types until pointers arrive, when it also accepts `nullptr` against a pointer. The condition "τ has values" excludes `void`, the type of a call to a function that returns nothing, and, from {secref}[lecture-6] on, the object types, whose values live in the store and never travel.

A *derivation* of a typing judgment is a tree of rule applications, as for evaluation. The derivation below types `x + 1 < 10` in the context Γ = \[x ↦ int\].

```
  Γ(x) = int
  ────────────── (T-Var)   ────────────── (T-Lit)
  Γ ⊢ x : int              Γ ⊢ 1 : int
  ─────────────────────────────────────── (T-Arith)   ─────────────── (T-Lit)
  Γ ⊢ x + 1 : int                                     Γ ⊢ 10 : int
  ──────────────────────────────────────────────────────────────────── (T-Rel)
  Γ ⊢ x + 1 < 10 : bool
```

# Commands and the Context

%%%
tag := "commands-context"
%%%

Commands do not have a type, but they change the context. The judgment Γ ⊢ c ⊣ Γ' states that the command c is well typed in Γ and produces the context Γ' for the commands that follow it. A declaration extends the context, a sequence threads it, and a block discards the extension, exactly as the environment behaves in the evaluation rules of Unit I.

```
Γ ⊢ e : τ'    τ' ≈ τ    τ has values           Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ
─────────────────────────────────── (T-Decl)   ───────────────────────────────── (T-Assign)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                         Γ ⊢ e₁ = e₂ ⊣ Γ

Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂                     Γ ⊢ c₁ … cₙ ⊣ Γ'
────────────────────────── (T-Seq)             ──────────────────── (T-Block)
Γ ⊢ c cs ⊣ Γ₂                                  Γ ⊢ { c₁ … cₙ } ⊣ Γ
```

The type checker of Core C++ implements these rules, one function per judgment, and rejects a program at the first rule that fails. A declaration whose initialiser has the wrong type is the simplest case.

```lean (name := declMismatch)
#eval (parseProgram "int main() { int x = true; return x; }").map check
```
```leanOutput declMismatch
Except.ok (Except.error (CoreCpp.TypeError.mismatch "initialiser of x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

An operator applied to the wrong type fails at its own rule, and the message names the operator and the type it received.

```lean (name := arithBool)
#eval (parseProgram "int main() { return (1 < 2) + 1; }").map check
```
```leanOutput arithBool
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

A condition that is not a boolean fails at `T-Cond`, even when C++ would convert the integer to a truth value. Core C++ has no such conversion.

```lean (name := condInt)
#eval (parseProgram "int main() { return 7 / 2 ? 1 : 0; }").map check
```
```leanOutput condInt
Except.ok (Except.error (CoreCpp.TypeError.mismatch "condition" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

A program that types goes through the checker without a message, and the declaration with `auto` takes the type of its initialiser.

```lean (name := autoBool)
#eval (parseProgram "int main() { auto y = 3 > 2; return y ? 1 : 0; }").map run
```
```leanOutput autoBool
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

# What a Type System Buys

%%%
tag := "type-system"
%%%

A *type system* is the set of typing rules of a language together with the guarantee they give. The guarantee of Core C++ is the one stated in {secref}[lecture-3]. Every derivation of a well typed program ends in a value or in `error`, and never gets stuck at a construction without a rule. A program that adds an `int` to a `bool` has no evaluation rule for that sum, and the type system rejects it before the evaluator meets it. A program that divides by zero has a rule, the one that produces `error`, and the type system lets it through, because the divisor is a value the checker does not know.

The distinction is the one between *static* and *dynamic* checking of {secref}[lecture-4]. The type system checks, before execution and for all executions at once, the properties that depend only on types. Everything that depends on values is checked during execution, by the rules that produce `error`. Core C++ moves as much as it can to the static side, but the boundary is fixed by what the checker can know. {numref}[tbl-static-dynamic] lists the situations of this unit on each side.

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
  * condition of `if` that is an `int`
  * statically
  * `T-If`
*
  * variable used outside its scope
  * statically
  * `T-Var`, Γ has no entry
*
  * field that the class lacks
  * statically
  * `T-Arrow`, in {secref}[lecture-6]
*
  * division by zero
  * dynamically
  * `DivZero`
*
  * `int` overflow
  * dynamically
  * `int32`
*
  * dereference of `nullptr`
  * dynamically
  * `LocDeref`, in {secref}[lecture-7]
*
  * index outside the vector
  * dynamically
  * `LocIndex`, in {secref}[lecture-7]
:::

{tabcap "tbl-static-dynamic"}[What the type system of Core C++ checks before execution and what the evaluation rules check during it.]

Languages differ in where they put the boundary. Python has no static checking, so every situation of the table is found during execution, if the program reaches it. C++ checks types statically, but accepts conversions Core C++ rejects, such as the integer condition above, and leaves the dynamic situations undefined instead of stopping the program. Lean, the language of the interpreter, has a type system rich enough to express, in the type of a function, properties Core C++ can only check at run time, and Unit VI returns to that point.{fnref}[soundness]

:::footnotes

{fnAnchor "soundness"}[] The guarantee that well typed programs never get stuck is called *soundness* of the type system, or type safety, and Pierce presents it for a small language as the pair of theorems progress and preservation.{margin}[B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, chapter 8.] For Core C++ the course states the property, checks it by inspection of the rule set, and does not prove it in Lean.

:::

# Exercises

%%%
tag := "exercises-5"
%%%

{exercise "exr-type-derivation"}[] Build the typing derivation of `(a && b) ? n : n + 1` in the context Γ = \[a ↦ bool, b ↦ bool, n ↦ int\], naming the rule at each step.

{exercise "exr-context-block"}[] Write the sequence of contexts Γ₀, Γ₁, … produced by `int x = 1; { bool b = x < 2; x = b ? 2 : 3; } x = x + 1;`, and say which context checks the last assignment.

{exercise "exr-static-or-dynamic"}[] For each situation, say whether Core C++ detects it statically or dynamically, and name the rule. A `return` with a `bool` in an `int` function. A `while` whose condition is `x` with `x` an `int`. A remainder by a variable that is zero. A call with two arguments to a function of one parameter.

{exercise "exr-cpp-accepts"}[] Write three programs that `g++` accepts and the type checker of Core C++ rejects, each for a different rule, and predict the value `g++` computes for each.

{exercise "exr-conditional-type"}[] The rule `T-Cond` requires the two branches to have the same type. Give a program in which the branches have different types, say what value C++ would compute for it, and explain why Core C++ prefers the rejection.

```lean -show
end Lecture5
```
