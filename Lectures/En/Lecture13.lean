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

#doc (Manual) "Lecture 13: Functions and Call by Value" =>

%%%
tag := "lecture-13"
%%%

```lean -show
namespace Lecture13
open CoreCpp
```

This lecture opens Unit IV, Abstraction. An abstraction gives a name and parameters to a piece of program so that it can be used many times with different arguments. The lecture reviews the two kinds of abstraction Core C++ has had since Unit I, functions and procedures, and gives the call rule its full reading. A call by value allocates a fresh location with a copy of each argument, runs the body in an environment that holds only the parameters, and frees the copies on return. The `return` command is a control result that rises to the call that consumes it.

*This lecture is also available as [presentation slides](../slides/lecture-13.en.html).*

# Abstraction

%%%
tag := "abstraction"
%%%

Every language offers ways to name a piece of program and reuse it. Watt calls them abstractions{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, chapter 5.] and classifies them by the phrase they abstract. A *function abstraction* names an expression, and its call is an expression that yields a value. A *procedure abstraction* names a command, and its call is a command that changes the store. Core C++ writes both as functions, with a result type for the first and `void` for the second, and {numref}[tbl-abstractions] gives the correspondence.

:::table +header
*
  * Abstraction
  * Abstracts
  * Call is
  * In Core C++
*
  * function
  * an expression
  * an expression with a value
  * `int f(…) { … return e; }`
*
  * procedure
  * a command
  * a command, an effect on σ
  * `void p(…) { … }`, called as `p(…);`
:::

{tabcap "tbl-abstractions"}[The two kinds of abstraction of Core C++.]

The *parameters* of an abstraction are the names its body uses for the values it receives, and the *arguments* are the expressions the call supplies. The relation between an argument and its parameter is the *parameter mechanism*, and the meaning of a call depends on it. Unit I fixed one mechanism, call by value. This lecture writes its rule in full, {secref}[lecture-14] adds call by reference, {secref}[lecture-15] adds abstractions as values, and {secref}[lecture-16] compares the mechanisms of other languages.

# The Call Rule

%%%
tag := "call-rule"
%%%

Let $`f` be declared as $`\tau\ f(\tau_1\ x_1, \ldots, \tau_k\ x_k)\ \{c\}`. A call $`f(e_1, \ldots, e_k)` under ρ and σ proceeds in four steps, and the rule records each one.

```
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c }) in the program
ρ, σ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ                    arguments, left to right
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, vᵢ),  σ'₀ = σₖ                          a fresh location with a copy of each value
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                                    the function environment
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''                                   the body runs to a return
────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓ₁, …, ℓₖ}                      the copies leave the store
```

The arguments are evaluated first, in the environment of the call and left to right, and every effect they have on the store is kept. Each value then receives a *fresh location*, and the parameter is bound to it. This is *call by value*, the parameter is a copy of the argument, and a write to the parameter never reaches the argument. The body runs under `ρ_f`, which holds *only the parameters*. Core C++ has no global variables, so nothing of the caller is visible inside the callee except through the values passed. The `return` yields the control ret v, and the call consumes it and produces v. Finally the locations of the parameters are removed from the store, the end of their lifetime.

The typing rule checks each argument against its parameter type, and the type of the call is the declared result type.

```
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ' with τᵢ' ≈ τᵢ for each i
────────────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

The program below calls `quadrado` with an argument that is itself an expression. The argument is evaluated to 7 before the body runs, and the parameter `n` is a fresh location holding 7.

```lean (name := quadrado)
def square : String :=
  "int quadrado(int n) { return n * n; }
   int main() { int a = 6; return quadrado(a + 1); }"

#eval (parseProgram square).map run
```
```leanOutput quadrado
Except.ok (Except.ok (CoreCpp.Val.int 49))
```

# The Parameter Is a Copy

%%%
tag := "copy"
%%%

The function `dobro` below assigns to its parameter. Under call by value the assignment writes to the copy, and the variable `x` of `main` keeps its value. The result adds the returned 42 to the unchanged 21.

```lean (name := dobro)
def double : String :=
  "int dobro(int n) { n = n * 2; return n; }
   int main() { int x = 21; return dobro(x) + x; }"

#eval match parseProgram double with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput dobro
    [], {} ⊢ 21 ⇒ 21, {}   (Lit)
  [], {} ⊢ int x = 21; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 21}   (Decl)
          [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 21}   (LocVar)
        [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ x ⇒ 21, {ℓ0 ↦ 21}   (Var)
              [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ n ⇒ₗ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ 21}   (LocVar)
            [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ n ⇒ 21, {ℓ0 ↦ 21, ℓ1 ↦ 21}   (Var)
            [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ 2 ⇒ 2, {ℓ0 ↦ 21, ℓ1 ↦ 21}   (Lit)
          [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ n * 2 ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ 21}   (Binary)
          [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ n ⇒ₗ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ 21}   (LocVar)
        [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 21} ⊢ n = n * 2; ⇒ normal, [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 42}   (Assign)
            [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 42} ⊢ n ⇒ₗ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ 42}   (LocVar)
          [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 42} ⊢ n ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ 42}   (Var)
        [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 42} ⊢ return n; ⇒ ret 42, [n ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ 42}   (Return)
      [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ dobro(x) ⇒ 42, {ℓ0 ↦ 21}   (Call)
        [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 21}   (LocVar)
      [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ x ⇒ 21, {ℓ0 ↦ 21}   (Var)
    [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ dobro(x) + x ⇒ 63, {ℓ0 ↦ 21}   (Binary)
  [x ↦ ℓ0], {ℓ0 ↦ 21} ⊢ return dobro(x) + x; ⇒ ret 63, [x ↦ ℓ0], {ℓ0 ↦ 21}   (Return)
[], {} ⊢ main() ⇒ 63, {}   (Call)
```

Three details of the trace deserve attention. The argument `x` is read in the environment of `main`, \[x ↦ ℓ0\], before the body starts. The body runs under \[n ↦ ℓ1\], an environment with one binding, to the fresh location ℓ1 that holds the copy 21. After the call the store is back to \{ℓ0 ↦ 21\}, the copy at ℓ1 has left it, and `x` still holds 21.

# Return as Control

%%%
tag := "return"
%%%

The `return e` command does not jump. It evaluates $`e` and yields the control ret v, and the rules of sequence, block and loop propagate that control upwards without running what follows, until the call rule consumes it. {secref}[lecture-11] gave those rules, `Seq-Ret`, `While-Ret` and the `if` and block rules that pass any control through. The call is the only rule that turns ret v back into a value.

A function whose body ends with the control normal has not returned. For a `void` function that is the ordinary end of a procedure, and the call yields the value void. For a function with a result type it is an `error`, because there is no value to produce.

```lean (name := semRetorno)
def noReturn : String :=
  "int f(int n) { if (n > 0) { return 1; } }
   int main() { return f(0); }"

#eval (parseProgram noReturn).map run
```
```leanOutput semRetorno
Except.ok (Except.error (CoreCpp.Error.missingReturn "f"))
```

The type checker does not detect this case, because it would need to know which paths of the body reach a `return`, a flow analysis outside the scope of the course. C++ leaves the same program undefined, and Core C++ gives it the result `error`.{fnref}[flow]

A procedure is called as a statement, and its value void is discarded by the rule `ExprStmt`.

```lean (name := nada)
def procedure : String :=
  "void nada() { int x = 1; }
   int main() { nada(); return 3; }"

#eval (parseProgram procedure).map run
```
```leanOutput nada
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

:::footnotes

{fnAnchor "flow"}[] A compiler that wants to reject the program at compile time computes, for each function, whether every path from the entry to the end of the body passes through a `return`. Java requires this analysis and rejects a method that can reach its end without returning a value. C++ only warns. Core C++ chooses the dynamic answer, the `error` result, and leaves the analysis as an exercise of Unit VI.

:::

# Static Checking of Calls

%%%
tag := "typing-calls"
%%%

The rule `T-Call` fixes what is checked before execution. The function must exist, the number of arguments must match, and each argument must have the type of its parameter, with the conversion of `nullptr` to a pointer type as the only tolerance. A call of `f` with a `bool` where an `int` is expected is rejected.

```lean (name := callType)
def wrongArgument : String :=
  "int f(int n) { return n; } int main() { return f(true); }"

#eval (parseProgram wrongArgument).map check
```
```leanOutput callType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument n of f" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

Inside the body, the parameters are the only variables in the initial context, \[x₁ ↦ τ₁, …, xₖ ↦ τₖ\], and the `return` expression is checked against the declared result type. The rule `T-Fun` of {secref}[lecture-4] records both conditions.

# Exercises

%%%
tag := "exercises-13"
%%%

{exercise "exr-trace-two-params"}[] Draw the derivation of `int soma(int a, int b) { return a + b; } int main() { return soma(2, 3); }` up to the body of `soma`, showing the two fresh locations and the environment of the call, and compare with the trace of the interpreter.

{exercise "exr-copy-pointer"}[] A parameter of pointer type is also a copy. Write a function `void zera(P* p)` that sets `p->a` to 0 and a function that assigns `nullptr` to its pointer parameter, and explain, by the rule `Call`, why the first has an effect visible in `main` and the second has not.

{exercise "exr-missing-return"}[] Write a function with two `if` commands whose paths all end in a `return` and one where a path does not, run both with the interpreter, and explain why the type checker accepts both.

{exercise "exr-recursion"}[] The call rule allocates fresh locations at each call. Trace `int f(int n) { if (n == 0) { return 0; } return n + f(n - 1); }` with `f(2)` and count the locations that exist when the innermost call returns.

{exercise "exr-argument-effects"}[] Write a call whose arguments have effects on the store, for instance through a function that increments a counter reached by a pointer, and explain by the rule `Call` in which store the body starts to run.

```lean -show
end Lecture13
```
