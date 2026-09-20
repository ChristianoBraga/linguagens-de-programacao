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

#doc (Manual) "Lecture 16: Parameter Evaluation" =>

%%%
tag := "lecture-16"
%%%

```lean -show
namespace Lecture16
open CoreCpp
```

This lecture closes Unit IV with the question of *when* an argument is evaluated. Core C++ and C++ evaluate every argument before the body runs, the *strict* or *eager* discipline. Other languages postpone the evaluation of an argument until the body needs it, the *lazy* discipline, of which call by name and call by need are the two forms. The lecture writes the rules of call by name as rules without counterpart in the core, contrasts them with the rules of Core C++, shows how a lambda simulates a postponed argument, and reviews the whole fragment of the language implemented up to this unit.

*This lecture is also available as [presentation slides](../slides/lecture-16.en.html).*

# Strict Evaluation

%%%
tag := "strict"
%%%

The rule `Call` of {secref}[lecture-13] evaluates every argument before the body starts, in the premises ρ, σᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ. Whether the body uses the parameter or not makes no difference. The function `primeiro` below ignores its second parameter, and the call still evaluates `10 / 0`, so the program ends in `error`.

```lean (name := primeiro)
def first : String :=
  "int primeiro(int a, int b) { return a; }
   int main() { return primeiro(1, 10 / 0); }"

#eval (parseProgram first).map run
```
```leanOutput primeiro
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

This is the meaning of *strict evaluation*, an argument is evaluated exactly once, before the call, and its effects and its errors happen whether or not the value is used. C++, Java, Python and Lean follow this discipline for function arguments.

Core C++ has three operators that do not. The conjunction, the disjunction and the conditional evaluate their second operand only when the first does not decide the result, by the rules `And-False`, `Or-True` and the two rules of `?:` of {secref}[lecture-8]. They are the built in *non strict* operators of the language, and the program below uses one of them to guard the division.

```lean (name := curto)
def guarded : String :=
  "int main() { int z = 0;
   return (z == 0 || 10 / z > 1) ? 1 : 0; }"

#eval (parseProgram guarded).map run
```
```leanOutput curto
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

# Call by Name

%%%
tag := "by-name"
%%%

*Call by name* is the discipline of ALGOL 60, in which an argument is not evaluated at the call. The parameter stands for the argument *expression*, and each use of the parameter in the body evaluates the expression again, in the environment of the call. Core C++ has no such construction, and the rule below is written for a hypothetical parameter `τ name x`, to show what would change.{margin}[P. Naur (ed.), *Revised Report on the Algorithmic Language ALGOL 60*, Communications of the ACM 6(1), 1963, pp. 1 to 17.]

```
f ↦ (τ f (τ₁ name x₁) { c })
ρ_f = [x₁ ↦ thunk(e₁, ρ)]                     the parameter is bound to the unevaluated argument and its environment
ρ_f, σ ⊢ c ⇒ ret v, ρ', σ'
──────────────────────────────────────────── (Call-Name)
ρ, σ ⊢ f(e₁) ⇒ v, σ'

ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Name)     every read of x evaluates e again
ρ, σ ⊢ x ⇒ v, σ'
```

Two things break the model of Core C++. The environment no longer maps identifiers to locations only, a parameter by name is bound to a pair of an expression and an environment, called a *thunk*. And a read of a variable may have effects and errors, because it evaluates an expression. With this discipline `primeiro(1, 10 / 0)` returns 1, since `b` is never read, and a parameter read twice evaluates its argument twice, which repeats any effect the argument has.

# Simulating a Postponed Argument

%%%
tag := "thunks"
%%%

The lambdas of {secref}[lecture-15] let a Core C++ program postpone an argument. Instead of a value, the caller passes a function of no parameters whose body is the argument expression, and the callee calls it when, and as many times as, it needs the value. The function `primeiro` below has that shape, and the call with `10 / z` returns 1, because the closure is never called.

```lean (name := primeiroPreguicoso)
def firstLazy : String :=
  "int primeiro(int a, std::function<int()> b) { return a; }
   int main() { int z = 0;
   return primeiro(1, [=]() -> int { return 10 / z; }); }"

#eval (parseProgram firstLazy).map run
```
```leanOutput primeiroPreguicoso
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

The closure plays the role of the thunk, and its captured copies play the role of the environment ρ₀ of the rule `Var-Name`. The difference is that the programmer writes the postponement, with `[=]() -> int { … }` at the call and `b()` at each use, where ALGOL 60 did it for every parameter.

The simulation also shows the repeated evaluation of call by name. The function `duasVezes` calls its argument twice, and the argument increments a counter reached through a captured pointer, so the two calls see 1 and 2 and the sum is 3. A discipline that evaluates the argument once and remembers the value, *call by need*, would give 2.

```lean (name := duasVezesEfeito)
def twiceEffect : String :=
  "class Caixa { public: int valor; };
   int duasVezes(std::function<int()> t) { return t() + t(); }
   int main() { Caixa* c = new Caixa(); c->valor = 0;
     return duasVezes([=]() -> int {
       c->valor = c->valor + 1; return c->valor; }); }"

#eval (parseProgram twiceEffect).map run
```
```leanOutput duasVezesEfeito
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

# Lazy Evaluation in Haskell

%%%
tag := "lazy"
%%%

Haskell evaluates every argument by need. An argument is evaluated the first time its value is required and never again, and an argument whose value is never required is never evaluated.{margin}[S. Peyton Jones, *The Implementation of Functional Programming Languages*, Prentice Hall, 1987, chapter 11.] The function `primeiro` in Haskell returns its first argument, and the call with a division by zero returns 1.

```
primeiro :: Int -> Int -> Int
primeiro a b = a

main = print (primeiro 1 (div 10 0))
```

The same program in Core C++ ends in `error`, as {secref}[strict] showed. The rule that describes Haskell's discipline is the rule `Call-Name` with one change, the thunk is replaced by its value after the first evaluation, so the second read of the parameter finds a value and evaluates nothing.

```
ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────────────── (Var-Need)     the first read updates the binding
ρ, σ ⊢ x ⇒ v, σ'    and the binding becomes x ↦ v
```

Call by need is only equivalent to call by name when the argument has no effects, which is the case in Haskell, where expressions do not change any store. In a language with assignment the two disciplines differ, as `duasVezes` showed, and that is one reason imperative languages keep the strict discipline for arguments. {numref}[tbl-disciplines] summarises.

:::table +header
*
  * Discipline
  * Argument evaluated
  * Effects of the argument
  * Language
*
  * strict, by value
  * once, before the call
  * once, always
  * Core C++, C++, Java, Python, Lean
*
  * by name
  * at each read of the parameter
  * repeated at each read
  * ALGOL 60
*
  * by need
  * at the first read, if any
  * once, if read
  * Haskell
*
  * by value with a closure
  * at each call of the closure
  * at each call
  * simulation in Core C++
:::

{tabcap "tbl-disciplines"}[The disciplines of parameter evaluation.]

# The Fragment of Unit IV

%%%
tag := "fragment-16"
%%%

Unit IV added to Core C++ the constructions of {numref}[tbl-fragment-16], each with its typing and evaluation rules and each implemented in the interpreter. The specification of the fragment is the document `spec-ud4.md` of the course, and the [blueprint](https://christianobraga.github.io/corecpp/) shows every rule beside the Lean function that implements it.

:::table +header
*
  * Construction
  * Rules
  * Lecture
*
  * call by value, `return`
  * `T-Call`, `Call`, `Return`
  * {secref}[lecture-13]
*
  * reference parameters `τ& x`
  * `T-Call` with ⊢ₗ, `Call` with an alias binding
  * {secref}[lecture-14]
*
  * `std::function<τ(…)>` types, lambdas `[=]`
  * `T-Lambda`, `Lambda`
  * {secref}[lecture-15]
*
  * calls of function values
  * `T-CallFn`, `CallFn`
  * {secref}[lecture-15]
*
  * capture by copy, read only
  * `T-LocVar` with the read only mark
  * {secref}[lecture-15]
:::

{tabcap "tbl-fragment-16"}[The constructions of Unit IV and their rules.]

Two design decisions of the fragment deserve a last word. A closure holds values, so no closure can hold a location that has left the store, and the language keeps its promise of no undefined behaviour. And a function value is copied when assigned or passed, exactly as an `int`, because a closure is a value and not an object.

```lean (name := functionValue)
def functionValue : String :=
  "int main() {
   std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
   std::function<int(int, int)> h = g; return h(10, 3); }"

#eval (parseProgram functionValue).map run
```
```leanOutput functionValue
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

# Exercises

%%%
tag := "exercises-16"
%%%

{exercise "exr-strict-effects"}[] Write a call whose argument has an effect and whose parameter is never read, run it, and explain by the rule `Call` why the effect happens anyway.

{exercise "exr-name-twice"}[] Under call by name, the body `return x + x;` with the argument `prox(c)` of {secref}[lecture-12] evaluates the call twice. Give the result for a counter starting at 0 under call by name, by need and by value.

{exercise "exr-simulate-if"}[] Write a function `seNao` that receives a `bool` and two values of type `std::function<int()>` and returns the value of one of them, and explain why the two arguments must be closures for the function to behave like `?:`.

{exercise "exr-need-rule"}[] The rule `Var-Need` updates a binding. Say what would have to change in the environment ρ of Core C++, which maps identifiers to locations, for such a rule to be written without thunks.

{exercise "exr-haskell-list"}[] In Haskell the expression `take 3 [1..]` returns the first three elements of an infinite list. Explain, by the discipline of call by need, why the program terminates, and why no Core C++ program can define such a list.

{exercise "exr-review"}[] For each construction of {numref}[tbl-fragment-16], write a program of at most five lines that is accepted by the type checker and one that is rejected, and name the rule that rejects it.

```lean -show
end Lecture16
```
