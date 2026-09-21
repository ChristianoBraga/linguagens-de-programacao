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

#doc (Manual) "Lecture 28: The Logic Paradigm" =>

%%%
tag := "lecture-28"
%%%

```lean -show
namespace Lecture28
open CoreCpp
open CoreCpp.Logic
```

The fourth paradigm is not a fragment of Core C++. Nothing in the core corresponds to a program that is a set of implications and a computation that is a search for a proof, so the course gives the paradigm a language of its own, small enough for one lecture. The lecture defines its terms, gives unification and the SLD resolution judgment in the notation used since {secref}[lecture-3], and shows why a derivation of that judgment is a proof and not merely a computation. Students meet the resolution again here, from the logic course, now as an operational semantics.

*This lecture is also available as [presentation slides](../slides/lecture-28.en.html).*

# A Program of Implications

%%%
tag := "clauses"
%%%

A program of the language is a set of *Horn clauses*, each an implication with one conclusion.

$$`\begin{array}{lcl} t & ::= & X \mid n \mid f(t_1, \ldots, t_k) \\ A & ::= & p(t_1, \ldots, t_k) \\ C & ::= & A \mid A \mathbin{\texttt{:-}} A_1, \ldots, A_m \\ P & ::= & C_1 \ldots C_n \\ G & ::= & A_1, \ldots, A_k \end{array}`

A *term* is a variable, an integer or a functor applied to terms, and a constant is a functor of no arguments. An *atom* is a predicate symbol applied to terms. A *clause* `A :- A₁, …, Aₘ` is read as the implication, if all the `Aᵢ` hold then `A` holds, and a clause with no body is a *fact*. A *query* is a list of atoms, and asking it means asking whether they all hold and with which values for their variables.

A name with a lowercase initial is a functor or a predicate symbol, one with an uppercase initial is a variable, `%` opens a comment and the full stop ends a clause. A list is written in the bracket notation, and the functor behind it is `.` over the constant that the source writes as an empty pair of brackets.

The whole of concatenation is two clauses. The first says that the empty list concatenated with `L` is `L`, the second that concatenating a list whose head is `H` gives a result whose head is `H`.

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

The two queries are the point of the paradigm. The clauses were written once, and they answer both the question of what the concatenation of two given lists is and the question of which pairs of lists concatenate to a given one. A function computes in one direction, a relation holds in all of them, and nothing in the program says which argument is the input.

# Unification

%%%
tag := "unification"
%%%

The device that makes a relation run in several directions is *unification*, the operation that makes two terms equal by binding variables. A *substitution* θ is a finite map from variables to terms, and the judgment is θ ⊢ s ≐ t ⇒ θ', read as, extending θ, the terms `s` and `t` unify with θ'.

$$`\dfrac{x \notin \mathrm{dom}\ \theta \qquad x \text{ does not occur in } t}{\theta \vdash X \doteq t \Rightarrow \theta[X \mapsto t]}\;\textsf{(U-Var)}`

$$`\dfrac{}{\theta \vdash n \doteq n \Rightarrow \theta}\;\textsf{(U-Num)}`

$$`\dfrac{\theta_0 = \theta \qquad \theta_{i-1} \vdash s_i \doteq t_i \Rightarrow \theta_i}{\theta \vdash f(s_1 \ldots s_k) \doteq f(t_1 \ldots t_k) \Rightarrow \theta_k}\;\textsf{(U-Fn)}`

Nothing else unifies. Two functors of different names or of different arities fail, and so do a number and a compound term. This is the algorithm of Robinson.{margin}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, Journal of the ACM 12(1), 1965, pp. 23 to 41.]

A variable unifies with a term.

```lean (name := unify1)
#eval unify [] (.var "X") (.fn "f" [.num 1])
```
```leanOutput unify1
some [("X", CoreCpp.Logic.Term.fn "f" [CoreCpp.Logic.Term.num 1])]
```

Unification is symmetric in the sense that both sides may carry variables, and one call binds them all.

```lean (name := unify2)
#eval unify [] (.fn "par" [.var "X", .num 2]) (.fn "par" [.num 1, .var "Y"])
```
```leanOutput unify2
some [("Y", CoreCpp.Logic.Term.num 2), ("X", CoreCpp.Logic.Term.num 1)]
```

The side condition of the rule `U-Var`, that `X` does not occur in `t`, is the *occurs check*, and it is what keeps a substitution acyclic. Without it, unifying `X` with `f(X)` would produce a binding whose resolution never ends.

```lean (name := unify3)
#eval unify [] (.var "X") (.fn "f" [.var "X"])
```
```leanOutput unify3
none
```

Most Prolog systems switch the occurs check off, because it costs time on every binding and the programs that need it are rare, and they accept an unsound answer in exchange. The language of this course keeps it on, since the course presents the algorithm as Robinson wrote it.{fnref}[occurs]

:::footnotes

{fnAnchor "occurs"}[] The ISO standard leaves the behaviour of a unification that would create a cyclic term undefined, which is the same device C++ uses for the situations of {secref}[lecture-4], and for the same reason, the cost of the check. A system that omits it may loop, print a cyclic term or produce a wrong answer, and the choice of the course is to pay the cost and keep the rule as written.

:::

# SLD Resolution

%%%
tag := "sld"
%%%

The meaning of a query is given by one judgment, in the notation used since {secref}[lecture-3]. The judgment is P, θ ⊢ G ⇒ θ', read as, under the program P and the substitution θ, the goal list G succeeds with the answer θ'.

$$`\dfrac{}{P, \theta \vdash \varepsilon \Rightarrow \theta}\;\textsf{(SLD-Empty)}`

$$`\dfrac{\begin{array}{c} (H \mathbin{\texttt{:-}} B_1 \ldots B_m) \text{ a fresh variant of a clause of } P \\ \theta \vdash A \doteq H \Rightarrow \theta_1 \qquad P, \theta_1 \vdash B_1 \ldots B_m\, G \Rightarrow \theta' \end{array}}{P, \theta \vdash A\, G \Rightarrow \theta'}\;\textsf{(SLD-Resolve)}`

Three things are packed into the second rule. The selected atom is the leftmost one, which is written into the shape of the conclusion. The clause is *renamed apart* before use, so that one use shares no variable with another, which is what lets a recursive predicate call itself. And the body of the clause is placed in front of the rest of the goals, so the search goes depth first.

Backtracking is not in the rules, it is in the search. The rule says that *some* clause of P applies, and an implementation must try them, in the order they are written, and take the next one when a branch fails. That separation is worth stating aloud, because the rules give the meaning and the search gives the strategy, and a different strategy over the same rules is a different Prolog with the same answers.

Arithmetic is not relational, and three built in predicates say so.

$$`\dfrac{\mathrm{eval}(\theta, t) = n \qquad \theta \vdash s \doteq n \Rightarrow \theta_1 \qquad P, \theta_1 \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \mathbin{\texttt{is}} t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Is)}`

$$`\dfrac{\mathrm{eval}(\theta, s) = m \qquad \mathrm{eval}(\theta, t) = n \qquad m \bowtie n \qquad P, \theta \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \bowtie t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Compare)}`

The rule `SLD-Is` evaluates its right side and unifies the result with its left side, so `is` runs in one direction only, unlike every other predicate. A term with an unbound variable has no arithmetic value, and the goal that asked for one fails. The factorial of {secref}[lecture-1] shows both the recursion and the arithmetic.

```lean (name := factQ)
def fatPl : String :=
  "fatorial(0, 1).
   fatorial(N, F) :- N > 0, M is N - 1, fatorial(M, G), F is N * G.
   ?- fatorial(5, F)."

#eval match Logic.parse fatPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput factQ
?- fatorial(5, F).
F = 120
```

The first clause is the base case, and the second guards itself with `N > 0` so that the two do not overlap. Reading the second as an implication, if `N` is positive, `M` is `N` minus one, the factorial of `M` is `G` and `F` is `N` times `G`, then the factorial of `N` is `F`. The program is the definition, and the search is what turns the definition into an answer.

# A Derivation Is a Proof

%%%
tag := "proof"
%%%

Everything above is a computation. What makes it a *logic* paradigm is that the computation is also a proof, and the correspondence is exact enough to state.

Read each clause `A :- A₁, …, Aₘ` as the universally quantified implication from the conjunction of the bodies to the head. Read the query `G` as the question whether the existential closure of the conjunction of its atoms follows from the program. A derivation of P, θ ⊢ G ⇒ θ' then corresponds to a refutation of the negation of that existential, each step of `SLD-Resolve` being one resolution step between the current goal and a clause, with unification as the most general unifier the resolution rule asks for. The answer θ' is the witness the existential asked for.

This is the resolution the logic course presented,{margin}[Course 09006, Lógica Matemática, IME, unit on logic programming.] and the only novelty here is the restriction that makes it efficient, that clauses are Horn, that the selected atom is the leftmost and that the search is depth first. Kowalski's reading of a clause as both a statement and a procedure is what the name of the paradigm records.{margin}[R. Kowalski, *Predicate Logic as Programming Language*, IFIP Congress, 1974, pp. 569 to 574.]

Two limits follow from the strategy rather than from the rules. A program that is *left recursive*, whose clause calls itself on the same goal before doing anything, has an infinite derivation and no finite one, so the search does not terminate. The implementation of the course bounds the depth of the derivation and reports no answer, which is the same accommodation {secref}[lecture-3] made for `while (true)`, the semantics has no derivation and the tool must stop somehow.

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

The answer `false` is the honest report of the bounded search, and it is not the same as saying that `q(1)` does not hold. A real Prolog loops here. Negation, the cut, assert and retract are outside the language of the course, and each of them would need a rule the judgment does not have.

# Exercises

%%%
tag := "exercises-28"
%%%

{exercise "exr-logic-member"}[] Write the two clauses of membership in a list, and give the three answers of the query that asks for the elements of a three element list. Say which clause each answer comes from.

{exercise "exr-logic-reverse"}[] Define the reversal of a list with concatenation, and say in which directions your definition works and in which it does not terminate.

{exercise "exr-logic-derivation"}[] Draw on paper the derivation of the query on the factorial with argument 2, with one application of `SLD-Resolve` per line, and mark the substitution after each step.

{exercise "exr-logic-occurs"}[] Give a query whose answer differs with and without the occurs check, and say what a system that omits it would print.

{exercise "exr-logic-is"}[] Explain why the query that asks for an `N` with `5 is N + 1` fails, and rewrite the factorial so that the query that asks for the `N` whose factorial is 120 would work, or argue that it cannot with the rules given.

{exercise "exr-logic-order"}[] Swap the last two goals of the recursive clause of the factorial and explain, from the rule `SLD-Is`, what changes. Then swap the two clauses and explain what changes in the search but not in the answers.

```lean -show
end Lecture28
```
