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

#doc (Manual) "Lecture 29: Four Paradigms, One Problem" =>

%%%
tag := "lecture-29"
%%%

```lean -show
namespace Lecture29
open CoreCpp
open CoreCpp.Logic
```

The last lecture puts one problem in four paradigms and compares them by the criteria the course has used since the beginning. The comparison is the second goal of the syllabus, and it is worth something here only because the first goal came first. Each of the four programs is read through rules the course wrote, so the comparison is between meanings and not between impressions.

*This lecture is also available as [presentation slides](../slides/lecture-29.en.html).*

# The Problem

%%%
tag := "problem"
%%%

The sum of the even numbers from 1 to n. The problem is small on purpose, because the comparison should be about how each paradigm says a thing and not about which is best at a hard thing. It has the three parts that a comparison needs, an accumulation, a filter and a repetition, and each paradigm expresses the three differently.

The imperative version accumulates in a variable and repeats with a loop.

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

The object oriented version of {secref}[lecture-26] makes the accumulator the state of an object and the filter a `virtual` method, so a new filter is a new class. The functional version of {secref}[lecture-27] makes the accumulator a parameter and the filter a function value, so a new filter is a new argument. The logic version states the relation between a number and the sum, with one clause per case of the filter.

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

The four programs are in the repository, three under `examples/` and one under `examples/logic/`, and all four give 30.

# The Comparison

%%%
tag := "paradigm-comparison"
%%%

{numref}[tbl-compare] answers the four questions the course has asked of every construction since {secref}[lecture-1], for each paradigm, over these four programs.

:::table +header
*
  * Criterion
  * Imperative
  * Object oriented
  * Functional
  * Logic
*
  * How state is expressed
  * a variable, a location of σ written repeatedly
  * a field of an object, a location that outlives the call
  * a parameter, a location written once
  * no state, a substitution grows as the search goes
*
  * How abstraction is expressed
  * the function, called by name
  * the method, selected by the class tag
  * the function value, passed as an argument
  * the predicate, selected by unification with the head
*
  * How repetition is expressed
  * the loop, with the rule that recurs on its own conclusion
  * the loop, over a collection of objects
  * the recursive call
  * the recursive clause
*
  * What the type system checks
  * the type of every expression and every assignment
  * the above, and visibility, dispatch and subtyping
  * the above, and the type of every function value
  * nothing, the language is untyped
*
  * What the semantics guarantees
  * a stack discipline for σ, no dangling location
  * every heap location is reached by a pointer or by `this`
  * the store is written once, referential transparency
  * an answer is a proof of the query from the clauses
*
  * Where the extension point is
  * the body of the function
  * the class hierarchy
  * the argument list
  * the clause set
:::

{tabcap "tbl-compare"}[The four paradigms over the same problem, by the criteria of the course.]

Three readings of the table are worth stating.

*The last row is the same freedom spent four ways.* Each paradigm has one place where a program is easy to extend without touching what is written, and it is a different place in each. That is the practical content of the choice of a paradigm, and it explains why a program often mixes them, as {secref}[lecture-1] said and as C++ allows.

*The fifth row is what the course added.* A comparison that stopped at the first four rows is the one a textbook makes, and it is defensible. The fifth is possible only because each paradigm was read through rules, and it is the one that says what a program of that style cannot do, not merely what it does not usually do.

*The fourth row has an outlier.* The logic language of {secref}[lecture-28] checks nothing before it runs, so a goal that no clause matches simply fails, indistinguishable from a goal that is false. A typed logic language exists, and the choice here follows Prolog.

# What the Seven Units Built

%%%
tag := "closing"
%%%

The course began with a question, what does a construction of a programming language mean, and answered it the same way twenty nine times, with a judgment and a rule. {numref}[tbl-units] is the ledger.

:::table +header
*
  * Unit
  * What it added to the core
  * What it added to the semantics
*
  * I
  * the grammar and the abstract syntax
  * the four judgments, ρ and σ
*
  * II
  * types, classes with fields, pointers, vectors
  * Γ ⊢ e : τ, the values of the heap
*
  * III
  * the local reference, the attributes of a variable
  * scope as the restoration of ρ, lifetime as removal from σ
*
  * IV
  * reference parameters, lambdas, `std::function`
  * the closure, the call rules
*
  * V
  * methods, constructors, destructors, inheritance
  * `this`, dispatch, `delete`
*
  * VI
  * overloading, operator members, templates
  * resolution in Γ, instantiation by substitution
*
  * VII
  * nothing
  * the fragments and SLD resolution
:::

{tabcap "tbl-units"}[What each unit added to Core C++ and to its semantics.]

Three things are worth carrying away.

*One model of memory, from the first rule to the last.* ρ maps identifiers to locations and σ maps locations to values, and that decision, taken in {secref}[lecture-3] before there was anything to store, is why the reference of {secref}[lecture-10], the closure of {secref}[lecture-15] and the object of {secref}[lecture-18] each cost one rule instead of a rewriting of all of them.

*No undefined behaviour, paid for construction by construction.* Every place where C++17 says nothing, Core C++ says `error` or rejects the program. The eight `error` results are the price, and the reward is that every question about a program of the core has an answer the rules give.

*The rules run.* Every rule of the course is a case of a Lean function, every derivation in these notes was printed by the interpreter, and every example was compared with `g++`. That is what keeps the rules honest, and it is the part of the method the course would defend first.

What the course did not do is also worth naming. It proved nothing. The properties of {secref}[lecture-25] to {secref}[lecture-27], the progress of {secref}[lecture-3] and the LL(1) claim of {secref}[lecture-2] are all verified by inspection, and a Lean proof of any of them is a natural next step for a student who wants one. Divergence has no derivation, and the semantics is silent about programs that do not terminate. And Core C++ is a subset, so the constructions of C++ it leaves out, the ones of the discrepancy table, were shown in real C++ and never modelled.

# Exercises

%%%
tag := "exercises-29"
%%%

{exercise "exr-case-fifth"}[] Add a fifth column to {numref}[tbl-compare] for Python, and fill the six rows from what the course said about dynamic typing. Say which row Python shares with no other column.

{exercise "exr-case-extend"}[] Extend all four versions of the case study with a second filter, the multiples of three, so that the program sums the numbers that pass either. Say for each version how many lines changed and which of them are in code that already existed.

{exercise "exr-case-mix"}[] Write a version of the case study that lies in no fragment, using an object and a lambda together, and say what it gains over both. Then say what claim of {secref}[lecture-26] and of {secref}[lecture-27] it gives up.

{exercise "exr-case-semantics"}[] For each of the four versions, say what the semantics of the course guarantees about it that it does not guarantee about the other three, and give a program that shows the difference.

{exercise "exr-case-invariant"}[] The imperative version has a loop invariant. State it, and then state the corresponding property of the functional version and of the logic version. Say which of the three is a specification and which is the program itself.

{exercise "exr-case-directions"}[] The logic version answers the query with the first argument given. Say what happens when the second is given instead, explain the result from the rule `SLD-Is`, and change the program so that both directions work, or argue that they cannot.

```lean -show
end Lecture29
```
