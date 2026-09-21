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

#doc (Manual) "Lecture 25: The Imperative Paradigm" =>

%%%
tag := "lecture-25"
%%%

```lean -show
namespace Lecture25
open CoreCpp
```

This lecture opens the last unit, in which the four paradigms are compared. The comparison rests on a single device. Three of the four paradigms are *fragments* of Core C++, that is, the language with some constructions forbidden, and a fragment is worth studying because forbidding a construction buys a property the whole language does not have. The lecture defines the device, gives the imperative fragment and states what its restriction buys.

*This lecture is also available as [presentation slides](../slides/lecture-25.en.html).*

# A Paradigm as a Restriction

%%%
tag := "restriction"
%%%

A *paradigm* is a programming style characterised by the constructions it favours, as {secref}[lecture-1] said. Twenty four lectures later the course can say something sharper. Core C++ holds the constructions of three paradigms at once, the imperative, the object oriented and the functional, so a program written in one of those styles is a Core C++ program that stays away from the constructions of the other two. That observation turns a style into a mathematical object.

A *fragment* of Core C++ is a set of forbidden constructions. A program *lies in* the fragment when no declaration of the program mentions one of them.

$$`\dfrac{\text{no declaration of } p \text{ mentions a construction that } f \text{ forbids}}{p \in f}\;\textsf{(Frag)}`

Three remarks fix what a fragment is not. It is not a grammar, because no production changes, and a program outside a fragment is still a Core C++ program with exactly the meaning the earlier units gave it. It is not a type system, because a program outside a fragment is not wrong, only written in another style. And it is not a sublanguage that the interpreter runs differently, because the evaluation rules do not change either.

What changes is what can be *said* about a program. The rules of Core C++ admit `error` in eight ways, and a fragment that forbids `delete` rules three of them out for every program in it. The rules leave the evaluation order of `f() + g()` to a choice, and a fragment without assignment makes the choice invisible. The rest of this unit is that exchange, one paradigm at a time, forbid this and gain that.

The predicate is a walk over the abstract syntax, and the interpreter runs it.

```lean (name := fragCheck)
def gcd : String :=
  "int gcd(int a, int b) {
    while (b != 0) { int t = b; b = a % b; a = t; }
    return a;
  }
  int main() { int x = gcd(48, 18); int& y = x; y = y + 1; return y; }"

#eval (parseProgram gcd).map (fragment .imperative)
```
```leanOutput fragCheck
Except.ok (Except.ok ())
```

# The Imperative Fragment

%%%
tag := "imperative"
%%%

The imperative fragment keeps what the first four units built and nothing else. {numref}[tbl-imperative] lists both sides.

:::table +header
*
  * Admitted
  * Forbidden
*
  * `int`, `bool`, `void`
  * class, pointer, vector and function types
*
  * variables, declaration with initialiser, `auto`
  * `new`, `delete`
*
  * the local reference `τ& y = e`, assignment
  * `this`, field access, dereference, indexing
*
  * block, `if`, `while`, `for`, `return`, expression statement
  * method call, class, class template
*
  * first order functions, by value and by reference
  * lambda, `std::function`, call through a function value
:::

{tabcap "tbl-imperative"}[What the imperative fragment admits and what it forbids.]

The program of {secref}[restriction] lies in the fragment, and it is an ordinary imperative program, a loop with two variables, a function, a local reference and an assignment.

```lean (name := mdcRun)
#eval (parseProgram gcd).map run
```
```leanOutput mdcRun
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

A program that declares a class does not lie in the fragment, and the checker names the construction and the declaration in which it occurs.

```lean (name := fragReject)
def comClasse : String :=
  "class C { public: int v; };
   int main() { C* c = new C(); return c->v; }"

#eval (parseProgram comClasse).map (fragment .imperative)
```
```leanOutput fragReject
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class C" })
```

The vector is forbidden too, which deserves a word, because a vector is not an object in the usual sense of the paradigm. Core C++ has no array, so the only sequence it offers is `std::vector`, and the only way to get one is `new`. Admitting the vector would therefore admit the heap, and the heap is exactly what the next section says the fragment does not have. The price is that an imperative program of the fragment has no composite data, and the course pays it knowingly.

```lean (name := fragVector)
def comVetor : String :=
  "int main() {
     std::vector<int>* v = new std::vector<int>(2);
     return 0;
   }"

#eval (parseProgram comVetor).map (fragment .imperative)
```
```leanOutput fragVector
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "pointer type", site := "function main" })
```

# What the Restriction Buys

%%%
tag := "stack"
%%%

The whole language allocates locations in two ways. A declaration and a parameter binding allocate one each, and both are released when the block or the call that made them ends. A `new` allocates as many as an object has fields, and only a `delete` releases them. The imperative fragment has no `new`, so only the first way remains, and the store becomes a stack.

Three statements follow, all by inspection of the rules the fragment admits, none of them a Lean proof.

*Every value in σ is basic.* The values of Core C++ are `int`, `bool`, `void`, a location, `null`, an object, a vector and a closure. The fragment has no construction that produces any of the last five. A declaration stores the value of its initialiser, an expression of the fragment, and every expression rule of the fragment produces an `int` or a `bool`.

*The store follows a stack discipline.* Reading the rules `Decl`, `Block` and `Call` together, a location enters σ at a declaration or at a parameter binding and leaves it at the exit of the block or of the call that is its scope, in the reverse order of entry. Nothing else touches the domain of σ.

*A dangling location is unreachable.* An expression of the fragment reaches a location in one way only, through ρ, by the rule `LocVar`. Since ρ binds a name only while the location is live, the `error` result `danglingLocation` cannot arise. Two of the eight `error` results of Core C++, the double `delete` and the access after `delete`, disappear with it, and the `delete` through a base pointer disappears with the classes.

This is the shape of every claim in this unit. The fragment is smaller, so fewer rules apply, so more can be said.

A fair reading also names what the fragment loses. Without the heap, no data structure outlives the function that built it, so an imperative program of the fragment computes over what fits in its variables. That is why the object oriented fragment of {secref}[lecture-26] exists, and why C, which is the imperative language par excellence, has pointers.

# Control

%%%
tag := "control"
%%%

The other half of the paradigm is control. The imperative fragment inherits the three forms of {secref}[lecture-11], the sequence, the selection and the repetition, and the rule `While-T` that recurs on its own conclusion is the one that gives the loop its meaning. A program of the fragment is therefore read as a sequence of state changes in time, and its meaning is the final store.

This is worth setting against {secref}[lecture-27]. There, the same computation is a term whose value does not depend on time at all, and the loop becomes a recursive call. The two readings meet in the same semantics, with the same ρ and the same σ, which is the point of having written one set of rules for the whole language.

# Exercises

%%%
tag := "exercises-25"
%%%

{exercise "exr-frag-classify"}[] Run the three fragment checks over every program in `examples/` and build the table of which example lies in which fragment. Two of them lie in no fragment. Say which constructions put them outside all three.

{exercise "exr-frag-argue"}[] Give a program of the imperative fragment whose final store holds four locations, and give the order in which they enter and leave σ. Confirm it with `bin/corecpp trace`.

{exercise "exr-frag-error"}[] Of the eight `error` results of Core C++, say which ones a program of the imperative fragment can still produce, and give a program for each.

{exercise "exr-frag-reference"}[] The local reference is admitted in the imperative fragment and forbidden in the functional one. Argue both decisions from the property each fragment claims.

{exercise "exr-frag-vector"}[] Suppose Core C++ had the array `int a[10]`, with the array living in the frame of its declaration. Say which of the three statements of {secref}[stack] would survive if the imperative fragment admitted it, and which would need a new argument.

{exercise "exr-frag-extend"}[] Write the forbidden set of a fragment that admits the heap but not the class, that is, `new std::vector<int>` and pointers to vectors but no user defined class. State one property that fragment has and the object oriented one does not.

```lean -show
end Lecture25
```
