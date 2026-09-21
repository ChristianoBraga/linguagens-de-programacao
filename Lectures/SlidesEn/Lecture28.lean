/-
Slides of Lecture 28. Each top level section is a slide. The rules are
preformatted text in `tree` blocks.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "The Logic Paradigm" =>

Horn clauses, unification and SLD resolution as an operational semantics

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-28___-The-Logic-Paradigm/)

{cite}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, JACM 12(1), 1965.]

```lean -show
namespace Slides28
open CoreCpp
open CoreCpp.Logic
```

# §28.1 A program of implications

* Not a fragment of Core C++. Nothing in the core is a program of *implications* and a computation that is a *search for a proof*.

```tree
t ::= X | n | f(t₁, …, tₖ)        term
A ::= p(t₁, …, tₖ)                atom
C ::= A | A :- A₁, …, Aₘ          Horn clause, fact or rule
P ::= C₁ … Cₙ                     program
G ::= A₁, …, Aₖ                   query
```

* Lowercase initial is a functor or a predicate, uppercase is a *variable*.

* A clause is read as, if all the bodies hold then the head holds.

# §28.1 One definition, two questions

```lean (name := appendQ)
def appendPl : String :=
  "append([], L, L).
   append([H|T], L, [H|R]) :- append(T, L, R).
   ?- append([1, 2], [3, 4], R).
   ?- append(X, Y, [1, 2])."

#eval match Logic.parse appendPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput appendQ
?- append([1, 2], [3, 4], R).
R = [1, 2, 3, 4]
?- append(X, Y, [1, 2]).
X = []; Y = [1, 2]
X = [1]; Y = [2]
X = [1, 2]; Y = []
```

* A *function* computes in one direction. A *relation* holds in all of them, and nothing says which argument is the input.

# §28.2 Unification

```tree
x ∉ dom θ    x does not occur in t
────────────────────────────────── (U-Var)
θ ⊢ X ≐ t ⇒ θ[X ↦ t]

──────────────── (U-Num)
θ ⊢ n ≐ n ⇒ θ

θ₀ = θ    θᵢ₋₁ ⊢ sᵢ ≐ tᵢ ⇒ θᵢ
─────────────────────────────────── (U-Fn)
θ ⊢ f(s₁ … sₖ) ≐ f(t₁ … tₖ) ⇒ θₖ
```

* Robinson's algorithm. It is what makes a relation run in several directions, because it binds the variables of the query *and* of the clause at once.

# §28.2 The occurs check

```lean (name := unify3)
#eval unify [] (.var "X") (.fn "f" [.var "X"])
```
```leanOutput unify3
none
```

* The side condition of `U-Var` keeps the substitution *acyclic*.

* Most Prolog systems switch it off, pay less and accept an unsound answer. This course keeps it on.

# §28.3 SLD resolution

```tree
──────────────── (SLD-Empty)
P, θ ⊢ ε ⇒ θ

(H :- B₁ … Bₘ) a fresh variant of a clause of P
θ ⊢ A ≐ H ⇒ θ₁    P, θ₁ ⊢ B₁ … Bₘ G ⇒ θ'
───────────────────────────────────────────────── (SLD-Resolve)
P, θ ⊢ A G ⇒ θ'
```

* The *leftmost* atom is selected, written into the shape of the conclusion.

* The clause is *renamed apart*, which is what lets recursion work.

* *Backtracking is not in the rules.* The rules give the meaning, the search gives the strategy.

# §28.3 Arithmetic is not relational

```tree
eval(θ, t) = n    θ ⊢ s ≐ n ⇒ θ₁    P, θ₁ ⊢ G ⇒ θ'
─────────────────────────────────────────────────── (SLD-Is)
P, θ ⊢ (s is t) G ⇒ θ'
```

```lean (name := factQ)
def fatPl : String :=
  "factorial(0, 1).
   factorial(N, F) :- N > 0, M is N - 1, factorial(M, G), F is N * G.
   ?- factorial(5, F)."

#eval match Logic.parse fatPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput factQ
?- factorial(5, F).
F = 120
```

# §28.4 A derivation is a proof

* Read a clause as a universally quantified implication, and a query as asking whether an existential follows from the program.

* A derivation is then a *refutation* of the negation of that existential, each step a resolution step, unification supplying the most general unifier.

* The answer is the *witness*. This is the resolution of the logic course, restricted to Horn clauses, leftmost selection and depth first search.

* Kowalski's reading, a clause is a *statement* and a *procedure* at once.

# §28.4 What the strategy costs

```lean (name := leftRec)
#eval match Logic.parse "q(X) :- q(X). ?- q(1)." with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput leftRec
?- q(1).
false
```

* A *left recursive* program has an infinite derivation and no finite one. A real Prolog loops.

* The implementation bounds the depth, the same accommodation the course made for `while (true)`.

* `false` is the report of a bounded search, *not* the claim that the goal is false.

# Summary

* A program is a set of *Horn clauses*, a query a list of atoms, and nothing says which argument is the input.

* *Unification* with the occurs check is what runs a relation in several directions.

* *SLD resolution* is one judgment, leftmost selection, and the search supplies the backtracking.

* A derivation *is a proof*, which is the content of the name of the paradigm.

* Out of scope. Negation, the cut, assert and retract, and the divergence of left recursion.

Exercises: see the [lecture notes](../en/Lecture-28___-The-Logic-Paradigm/).

```lean -show
end Slides28
```
