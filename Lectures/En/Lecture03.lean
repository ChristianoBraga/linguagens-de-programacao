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

#doc (Manual) "Lecture 3: Semantics" =>

%%%
tag := "lecture-3"
%%%

```lean -show
namespace Lecture3
open CoreCpp
```

This lecture introduces natural semantics, the notation in which the course writes the meaning of each construction of Core C++. It starts from the judgments and inference rules students know from natural deduction, presents the three semantic components, environment, store and values, and writes the evaluation rules of the expressions and commands of the implemented subset. The interpreter in Lean produces the derivation tree of each execution, and the lecture teaches how to read it.

*This lecture is also available as [presentation slides](../slides/lecture-3.en.html).*

# Judgments and Inference Rules

%%%
tag := "judgments"
%%%

In natural deduction, a *judgment* is a statement that can be derived, such as "from Γ one deduces φ", and an *inference rule* says that, from judgments already derived, the premises, another one is derived, the conclusion. A *derivation* is a tree of rule applications, with axioms at the leaves and the derived judgment at the root. Natural semantics uses exactly this form, with judgments about programs in place of judgments about formulas.

A judgment of natural semantics says that a construction, evaluated in a certain context, produces a certain result. The course writes judgments in the sequent style of Kahn,{margin}[G. Kahn, *Natural Semantics*, STACS 87, LNCS 247, pp. 22 to 39, Springer, 1987.] with the context left of ⊢, the construction right of it and the result after ⇒. A rule has the premises above a line and the conclusion below it, and a name on the right, by which derivations cite it.

# Environment, Store and Values

%%%
tag := "domains"
%%%

Three components describe the state of an execution of Core C++. The *environment* ρ is a finite map from identifiers to *locations* ℓ, the abstract addresses of the store. The *store* σ is a finite map from locations to *values*, and its domain is the set of live locations. The values of the current subset are the 32 bit integers, `int n`, and the booleans, `bool b`.

The separation between environment and store is the most important semantic decision of the course. An identifier does not denote a value, it denotes a location, and the value is in the store. Reading `x` is reading σ(ρ(x)). Assigning to `x` is writing at ρ(x). Two variables may denote the same location, which Unit III uses for references, and a location may live after the identifier goes out of scope, which Unit V uses for objects. Since the model enters from the first rule, no rule is rewritten when those constructions arrive.

The course uses four judgments, and {numref}[tbl-judgments] lists them.

:::table +header
*
  * Judgment
  * Reading
*
  * Γ ⊢ e : τ
  * expression e has type τ in the typing context Γ
*
  * ρ, σ ⊢ e ⇒ v, σ′
  * under ρ and σ, expression e evaluates to v and yields the store σ′
*
  * ρ, σ ⊢ e ⇒ₗ ℓ, σ′
  * under ρ and σ, expression e denotes the location ℓ
*
  * ρ, σ ⊢ c ⇒ r, ρ′, σ′
  * under ρ and σ, command c yields the control r, the environment ρ′ and the store σ′
:::

{tabcap "tbl-judgments"}[The four judgments of the semantics of Core C++.]

The store enters the evaluation of expressions because a function call inside an expression may change it. The output environment of a command exists so that a declaration extends ρ for the following commands. The *control* r of a command is `normal` or `ret v`, and the second case records that a `return` was executed and that the value v must rise to the call.

All dynamic judgments admit `error` in place of the result. The `error` is not a value of the language. No syntax of Core C++ produces, tests or catches it, and it propagates to the whole program. It corresponds, in C++, to the abnormal termination of the program, and replaces the undefined behaviour C++ leaves in those cases.

# Expressions

%%%
tag := "expressions"
%%%

A literal evaluates to its value and leaves the store unchanged. The integer literal goes through the partial operation int32, which returns the integer when it fits in 32 bits and `error` otherwise.

```
─────────────────────────── (Lit)      ──────────────────────── (BoolLit)
ρ, σ ⊢ n ⇒ int32 n, σ                  ρ, σ ⊢ b ⇒ bool b, σ
```

A variable denotes the location the environment gives it, and its value is the content of that location in the store. The location must be live.

```
ρ(x) = ℓ                              ρ, σ ⊢ x ⇒ₗ ℓ, σ    ℓ ∈ dom σ
────────────────────── (LocVar)       ─────────────────────────────── (Var)
ρ, σ ⊢ x ⇒ₗ ℓ, σ                       ρ, σ ⊢ x ⇒ σ(ℓ), σ
```

An arithmetic binary operator evaluates the left operand, then the right one in the store the first produced, and applies the operation. The left to right order is a choice of Core C++ where C++17 fixes no order. Division and remainder have one premise more, the divisor different from zero, and a rule of their own for the zero divisor, with `error` as result.

```
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

Conjunction and disjunction *short circuit*, so the second operand is evaluated only when the first does not decide the result. Each operator has two rules, one per value of the first operand.

```
ρ, σ ⊢ e₁ ⇒ bool false, σ₁
──────────────────────────────── (And-False)
ρ, σ ⊢ e₁ && e₂ ⇒ bool false, σ₁

ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
─────────────────────────────────────────────── (And-True)
ρ, σ ⊢ e₁ && e₂ ⇒ v, σ₂
```

The conditional `e₁ ? e₂ : e₃` follows the same pattern, with one rule per value of the condition, and only the chosen branch is evaluated.

The derivation below evaluates `x + 41` in the environment ρ = \[x ↦ ℓ₀\] and the store σ = \{ℓ₀ ↦ 1\}. It applies `Var`, which in turn applies `LocVar`, then `Lit`, and finally `Arith`.

```
  ρ(x) = ℓ₀
  ──────────────── (LocVar)
  ρ, σ ⊢ x ⇒ₗ ℓ₀, σ    ℓ₀ ∈ dom σ
  ──────────────────────────────── (Var)    ─────────────────── (Lit)
  ρ, σ ⊢ x ⇒ int 1, σ                       ρ, σ ⊢ 41 ⇒ int 41, σ
  ─────────────────────────────────────────────────────────────── (Arith)
  ρ, σ ⊢ x + 41 ⇒ int 42, σ
```

# Commands

%%%
tag := "commands"
%%%

A declaration `τ x = e` evaluates the initialiser, allocates a fresh location with the value and extends the environment. The operation alloc returns a location outside the domain of σ, and locations are never reused.

```
ρ, σ ⊢ e ⇒ v, σ′    (ℓ, σ″) = alloc(σ′, v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

An assignment evaluates the right side, then the location of the left side, and writes the value. The order, right before left, is the one C++17 fixes for assignment, and Core C++ keeps it.

```
ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

A sequence of commands carries the output environment of each command to the next, and a `ret` interrupts the sequence. A block runs its sequence, discards the extension of the environment and removes from the store the locations the sequence declared. The scope of a variable is thus the restoration of ρ, and its lifetime is the removal of the location from σ.

```
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

The `if` has two rules, one per value of the condition, and each branch is a block. The `while` has three. When the condition is false, the loop ends in `normal`. When it is true and the body ends in `normal`, the whole loop runs again, and the rule recurs on its own conclusion. When the body ends in `ret v`, the loop is interrupted.

```
ρ, σ ⊢ e ⇒ bool false, σ₁
──────────────────────────────────────── (While-F)
ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂    ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
────────────────────────────────────────────────────────────────────────────────────── (While-T)
ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
────────────────────────────────────────────────────── (While-Ret)
ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂
```

The `return e` evaluates the expression and yields the control `ret v`, which `Seq-Ret` and `While-Ret` propagate up to the function call that consumes it. Unit IV presents the rule of the call.

# The Derivation Tree of an Execution

%%%
tag := "trace"
%%%

Each function of the interpreter implements a judgment, and each case of each function implements a rule, with the rule written in the comment of the case. When tracing is on, each rule application records its conclusion with the name of the rule, at the depth at which it occurs in the derivation tree. Premises are recorded before the conclusion, so the tree appears in *post order*, indented by depth. The root is the last line.

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
[], {} ⊢ main() ⇒ 42, {}   (Call)
```

Reading starts at the root, the call of `main` with empty environment and store. One level up are the three commands of the body, and the declaration creates the location ℓ0. The assignment, in the middle lines, first evaluates `x + 41`, whose derivation is the one of {secref}[expressions], and only then the location of `x`, in the order the rule `Assign` fixes. The store at the `return` has ℓ0 ↦ 42, and the `return` yields the control `ret 42` that the call consumes. The call then frees the locals of `main`, so the final store is empty, and the result of the program is the value 42 alone. In the interpreter the two cases `Arith` and `Rel` appear under the common name `Binary`.

# Error, Determinism and Divergence

%%%
tag := "properties"
%%%

Three properties of the rule set deserve record. The first is that every derivation of a well typed program ends in a value or in `error`, because every well typed construction has an evaluation rule. Division by zero and `int` overflow end in `error`, and the interpreter returns that result in place of a value.

```lean (name := divZero)
#eval (parseProgram "int main() { return 10 / 0; }").map run
```
```leanOutput divZero
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

```lean (name := overflow)
def overflow : String :=
  "int main() { return 2147483647 + 1; }"

#eval (parseProgram overflow).map run
```
```leanOutput overflow
Except.ok (Except.error (CoreCpp.Error.overflow))
```

The second is *determinism*. The rules of each construction have mutually exclusive premises, so a program has at most one derivation and at most one result. In C++ the same program may have more than one result, because the standard leaves the evaluation order of `f() + g()` to the compiler, and Unit III shows the other derivation a compiler may choose.

The third is a limitation. The rule `While-T` recurs on its own conclusion, and a loop that does not terminate, such as `while (true) { }`, has no finite derivation. Natural semantics, being inductive, does not describe diverging programs, and in that case the interpreter does not terminate either. Leroy and Grall show how a coinductive semantics covers those programs,{margin}[X. Leroy and H. Grall, *Coinductive big-step operational semantics*, Information and Computation 207(2), 2009, pp. 284 to 304.] and the course states the limitation without correcting it.

# Static Semantics

%%%
tag := "static"
%%%

The judgment Γ ⊢ e : τ says that expression e has type τ in the context Γ, a finite map from identifiers to types. Its rules have the same form as the evaluation rules, but do not mention the store, because they are checked before execution. The rule of the arithmetic operators requires `int` on both operands.

```
Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)
Γ ⊢ e₁ ⊕ e₂ : int
```

The type checker rejects `1 + true` before any evaluation, and Unit II treats types in detail.

```lean (name := typeError)
def sumBool : String := "int main() { return 1 + true; }"

#eval (parseProgram sumBool).map check
```
```leanOutput typeError
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

# Exercises

%%%
tag := "exercises-3"
%%%

{exercise "exr-derivation-if"}[] Build on paper the derivation of `int main() { int x = 2; if (x % 2 == 0) { x = x / 2; } else { x = x - 1; } return x; }` and compare it with the tree the interpreter prints.

{exercise "exr-rule-do-while"}[] Write the evaluation rules of `do { c } while (e);`, with the body executed before the first test, without using the rules of `while`.

{exercise "exr-rule-plus-equals"}[] Write the rule of `x += e` in two versions, a direct one and one that reduces it to `x = x + e`, and say in which case the two give different results if `e` may change the store.

{exercise "exr-order"}[] The rule `Assign` evaluates the right side before the left one. Write the rule with the opposite order and give a Core C++ program in which the two orders produce different final stores. Consider that Unit IV adds function calls with effects.

{exercise "exr-divergence"}[] Explain why `int main() { while (true) { } return 0; }` has no derivation, and what happens when the interpreter runs it.

{exercise "exr-scope"}[] Run `int main() { int x = 1; { int y = 2; x = x + y; } return x; }` with the interpreter and explain, by the rule `Block`, what happens to the location of `y` at the end of the inner block. Then replace `return x` by `return y` and explain the message of the type checker.

```lean -show
end Lecture3
```
