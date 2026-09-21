/-
Slides of Lecture 29. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Four Paradigms, One Problem" =>

The case study, the comparison, and what the seven units built

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-29___-Four-Paradigms,-One-Problem/)

```lean -show
namespace Slides29
open CoreCpp
open CoreCpp.Logic
```

# §29.1 The problem

* The sum of the even numbers from 1 to n. Small on purpose, because the comparison is about *how each paradigm says a thing*.

* Three parts, an *accumulation*, a *filter* and a *repetition*, expressed differently by each.

```lean (name := caseImp)
def caseImp : String :=
  "int somaPares(int n) {
     int acc = 0;
     for (int i = 1; i <= n; i = i + 1) {
       if (i % 2 == 0) { acc = acc + i; }
     }
     return acc;
   }
   int main() { return somaPares(10); }"

#eval (parseProgram caseImp).map fun p => (fragment .imperative p, run p)
```
```leanOutput caseImp
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

# §29.1 The same problem, four ways

::::cols
:::col
{lbl}[Object oriented]

The accumulator is the state of an object, the filter a `virtual` method. A new filter is a *new class*.
:::
:::col
{lbl}[Functional]

The accumulator is a parameter, the filter a function value. A new filter is a *new argument*.
:::
::::

```lean (name := caseLogic)
def caseLogic : String :=
  "soma_pares(0, 0).
   soma_pares(N, S) :-
     N > 0, 0 =:= N mod 2,
     M is N - 1, soma_pares(M, T), S is T + N.
   soma_pares(N, S) :-
     N > 0, 1 =:= N mod 2,
     M is N - 1, soma_pares(M, S).
   ?- soma_pares(10, S)."

#eval match Logic.parse caseLogic with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput caseLogic
?- soma_pares(10, S).
S = 30
```

# §29.2 The comparison

:::table +header
*
  * Criterion
  * Imperative
  * Object oriented
  * Functional
  * Logic
*
  * State
  * a variable
  * a field of an object
  * a parameter
  * no state, a substitution
*
  * Abstraction
  * the function
  * the method, by tag
  * the function value
  * the predicate, by unification
*
  * Repetition
  * the loop
  * the loop over objects
  * the recursive call
  * the recursive clause
*
  * The type system checks
  * every expression
  * and visibility, dispatch, subtyping
  * and every function value
  * nothing
*
  * The semantics guarantees
  * a stack discipline for σ
  * every heap location reached by pointer or `this`
  * the store written once
  * an answer is a proof
*
  * The extension point
  * the function body
  * the class hierarchy
  * the argument list
  * the clause set
:::

# §29.2 Three readings

* *The last row is one freedom spent four ways.* Each paradigm has one place that is easy to extend, and it is a different place. That is why programs mix them.

* *The fifth row is what this course added.* A comparison that stops at the first four is the textbook one. The fifth says what a program of that style *cannot* do.

* *The fourth row has an outlier.* The logic language checks nothing, so a goal no clause matches simply fails.

# §29.3 What the seven units built

:::table +header
*
  * Unit
  * To the core
  * To the semantics
*
  * I
  * grammar and abstract syntax
  * the four judgments, ρ and σ
*
  * II
  * types, classes with fields, pointers, vectors
  * Γ ⊢ e : τ, the values of the heap
*
  * III
  * the local reference
  * scope as restoration of ρ, lifetime as removal from σ
*
  * IV
  * reference parameters, lambdas
  * the closure, the call rules
*
  * V
  * methods, constructors, inheritance
  * `this`, dispatch, `delete`
*
  * VI
  * overloading, operators, templates
  * resolution in Γ, instantiation by substitution
*
  * VII
  * nothing
  * the fragments and SLD resolution
:::

# §29.3 Three things to carry away

* *One model of memory, from the first rule to the last.* ρ to locations, σ to values, decided before there was anything to store. That is why the reference, the closure and the object cost *one rule each*.

* *No undefined behaviour, paid construction by construction.* Eight `error` results are the price, and every question about a program has an answer.

* *The rules run.* Every rule is a case of a Lean function, every derivation was printed, every example compared with `g++`.

# §29.3 And what it did not do

* *It proved nothing.* The properties of this unit, the progress of Lecture 3 and the LL(1) claim of Lecture 2 are verified *by inspection*. A Lean proof of any of them is the natural next step.

* *Divergence has no derivation.* The semantics is silent about programs that do not terminate.

* *Core C++ is a subset.* What the discrepancy table leaves out was shown in real C++ and never modelled.

# Summary

* One problem, four paradigms, and the comparison rests on rules rather than on impressions.

* Each paradigm puts the *extension point* somewhere different, which is the practical content of the choice.

* The fifth row of the table, what the semantics guarantees, is what reading each paradigm through rules made possible.

* Seven units, one model of memory, no undefined behaviour, and rules that run.

* What remains is proof, and the course leaves it as the next step.

Exercises: see the [lecture notes](../en/Lecture-29___-Four-Paradigms,-One-Problem/).

```lean -show
end Slides29
```
