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

#doc (Manual) "Lecture 27: The Functional Paradigm" =>

%%%
tag := "lecture-27"
%%%

```lean -show
namespace Lecture27
open CoreCpp
```

The functional fragment forbids the update. It keeps the expressions, the lambdas, the function values and the calls, and gives up the assignment, the loops and the heap. What it buys is the strongest property of the three, the store is written once, and two consequences follow that the rest of the language does not have, referential transparency and indifference to the evaluation order. The lecture states both, writes the case study of the unit in the fragment, and uses Haskell as the contrast where Core C++ stops.

*This lecture is also available as [presentation slides](../slides/lecture-27.en.html).*

# The Fragment

%%%
tag := "functional-fragment"
%%%

{numref}[tbl-functional] gives both sides.

:::table +header
*
  * Admitted
  * Forbidden
*
  * `int`, `bool`, `void`, `std::function`
  * assignment
*
  * literals, variable, operators, the conditional
  * `while`, `for`, expression statement
*
  * function call, call through a function value
  * the local reference, the reference parameter
*
  * the lambda `[=]`
  * class, class template, method call, `this`
*
  * declaration with initialiser, `auto`
  * `new`, `delete`, field access, dereference, indexing
*
  * block, `if`, `return`
  * pointer, vector and class types
:::

{tabcap "tbl-functional"}[What the functional fragment admits and what it forbids.]

A declaration survives, and it is worth saying why. In the fragment a declaration is not a variable in the imperative sense, it is a *let binding*, a name for the value of an expression, because nothing can write the location afterwards. The loop does not survive, so a program of the fragment iterates by recursion, and the expression statement does not survive either, since without update it could only be there for an effect the fragment does not have.

```lean (name := funCheck)
def escala : String :=
  "int soma(int n) {
     return n == 0 ? 0 : n + soma(n - 1);
   }
   std::function<int(int)> escala(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int aplica(std::function<int(int)> f, int v) {
     return f(v);
   }
   int main() {
     std::function<int(int)> triplo = escala(3);
     int s = soma(4);
     return aplica(triplo, s);
   }"

#eval (parseProgram escala).map fun p => (fragment .functional p, run p)
```
```leanOutput funCheck
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

The program has a recursive function, a function that returns a closure and a function that takes one, which between them are the whole paradigm. A loop or an assignment puts a program outside the fragment, and the checker says at which declaration.

```lean (name := funNoLoop)
def comLaco : String :=
  "int f(int n) {
     int a = 0;
     for (int i = 0; i < n; i = i + 1) { a = a + i; }
     return a;
   }
   int main() { return f(3); }"

#eval (parseProgram comLaco).map (fragment .functional)
```
```leanOutput funNoLoop
Except.ok (Except.error { frag := CoreCpp.Frag.functional, what := "for", site := "function f" })
```

```lean (name := funNoAssign)
def comAtrib : String :=
  "int main() { int x = 1; x = x + 1; return x; }"

#eval (parseProgram comAtrib).map (fragment .functional)
```
```leanOutput funNoAssign
Except.ok (Except.error { frag := CoreCpp.Frag.functional, what := "assignment", site := "function main" })
```

# The Store Is Written Once

%%%
tag := "write-once"
%%%

The whole language writes σ at a location in three places, the rule `Assign`, the constructor that a `new` runs and the destructor that a `delete` runs. The fragment has none of the three. A location therefore receives its value at the declaration or at the parameter binding that created it, by the rules `Decl` and `Call`, and no rule of the fragment writes it again.

Call this *write once*. It is not the same as saying that σ does not change, because a call still allocates locations for its parameters and releases them at the return. It is the stronger and more useful statement that no location ever holds two different values in its life.

Two consequences follow, both by inspection of the rules the fragment admits.

*Referential transparency.* Evaluating one expression twice under the same ρ and the same σ gives the same value. The argument is that the value of an expression is determined by the values of the locations its free variables denote, that those locations are live throughout, and that write once says their values do not change. The practical reading is that a name may be replaced by what it denotes, which is the licence every algebraic simplification of a functional program needs.

*Indifference to the evaluation order.* {secref}[lecture-12] fixed the order of the operands of `e₁ ⊕ e₂` from left to right, because a call inside an operand may change σ and C++17 leaves the choice to the compiler. In the fragment neither operand can change σ at a location the other reads, so the two orders give the same result, and the choice becomes invisible. A program of the fragment therefore has one meaning under Core C++ and under any C++ compiler, which is the sharpest form of the agreement the course has been after since {secref}[lecture-4].

The price is that the fragment cannot express a computation over a data structure, since it has no heap, and cannot express in place update at all. A functional language answers the first with immutable structures, lists and trees built once and shared, and the second by refusing the question. Core C++ cannot follow it there, because an object of Core C++ is always a mutable record of locations, and the honest statement is that the fragment is the paradigm in miniature.

# Recursion in Place of Iteration

%%%
tag := "recursion"
%%%

Without the loop, a repetition is a recursive call, and the correspondence is exact. A loop with an accumulator becomes a function with an accumulating parameter, and the invariant of the loop becomes the specification of the function. The case study of the unit shows it, with the filter passed as a function value.

```lean (name := caseFun)
def caseFun : String :=
  "int somaAte(std::function<bool(int)> p, int n) {
     return n == 0 ? 0 : (p(n) ? n : 0) + somaAte(p, n - 1);
   }
   int main() {
     std::function<bool(int)> par = [=](int i) -> bool { return i % 2 == 0; };
     return somaAte(par, 10);
   }"

#eval (parseProgram caseFun).map fun p => (fragment .functional p, run p)
```
```leanOutput caseFun
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

The two versions of the case study, this one and the object oriented one of {secref}[lecture-26], place the extension point differently. Here the criterion is an argument, so a new criterion is a new value at the call site and `somaAte` does not change. There it is a `virtual` method, so a new criterion is a new class and `junta` does not change. The two are the same design freedom, spent in different currency.

One cost of the recursive form is visible in the derivation. Each call allocates the locations of its parameters and releases them at the return, so a recursion of depth ten puts ten frames in σ at once, where the loop reuses one. A functional language answers with tail call elimination, which Core C++ does not have and the course does not claim.

# Where Core C++ Stops, and Haskell Goes On

%%%
tag := "haskell"
%%%

Three things a functional language offers lie outside Core C++, and the course shows them in Haskell rather than pretending the core has them.

*Immutable data.* A list in Haskell is built once and shared, so a function that adds an element returns a new list that shares the old one, and write once holds for data as well as for locations. The fragment has no data at all, which is the gap.

*Laziness.* {secref}[lecture-16] gave call by name as a rule without a counterpart in the core, and Haskell evaluates by need, so an argument is evaluated at most once and only if used. That is what lets a Haskell program define an infinite list and take ten elements of it.

*Algebraic data types and pattern matching.* A sum type with a `case` is how a functional language writes what Core C++ writes with a class hierarchy and dispatch. The comparison is the one of {secref}[lecture-23], and the two are dual, one is easy to extend with new cases and hard with new operations, the other the reverse.

None of the three changes the semantics the course has written. They are the reason the paradigm is worth a language of its own rather than a fragment of another, and saying so plainly is more useful than stretching Core C++ to imitate them.

# Exercises

%%%
tag := "exercises-27"
%%%

{exercise "exr-fun-iterative"}[] Write the factorial in the functional fragment, with an accumulating parameter, and give the loop invariant of the imperative version as the specification of your function.

{exercise "exr-fun-order"}[] Give two programs, one in the functional fragment and one outside it, in which `f() + g()` has one value in the first and two possible values in C++ for the second. Say which rule of the fragment rules the second case out.

{exercise "exr-fun-transparency"}[] Take the case study and replace `par` by the lambda itself at the call site. Argue from write once that the two programs have the same value, and confirm it with the interpreter.

{exercise "exr-fun-depth"}[] Print the derivation of `somaAte(par, 3)` and count the locations live in σ at the deepest point. Say how many the loop version of {secref}[lecture-25] has at its deepest point.

{exercise "exr-fun-capture"}[] The lambda of the case study captures nothing. Write one that captures a bound from the enclosing scope, and explain, from the rule `Lambda`, why the capture cannot break write once.

{exercise "exr-fun-haskell"}[] Write the case study in Haskell with `filter` and `sum`, and say which of the three things of {secref}[haskell] your version uses.

```lean -show
end Lecture27
```
