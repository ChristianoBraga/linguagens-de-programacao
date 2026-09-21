/-
Slides of Lecture 25. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "The Imperative Paradigm" =>

A paradigm as a fragment of the core, and what the restriction buys

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-25___-The-Imperative-Paradigm/)

```lean -show
namespace Slides25
open CoreCpp
```

# §25.1 A paradigm as a restriction

* Core C++ holds the constructions of three paradigms at once. A program in one style *stays away* from the constructions of the other two.

* A *fragment* is a set of forbidden constructions. A program lies in it when no declaration mentions one.

```tree
no declaration of p mentions a construction that f forbids
───────────────────────────────────────────────────────── (Frag)
                        p ∈ f
```

* Not a grammar, not a type system, not another interpreter. The *rules do not change*.

* What changes is what can be *said* about the program.

# §25.2 The imperative fragment

::::cols
:::col
{lbl}[Admitted]

* `int`, `bool`, `void`

* variables, `auto`, the local reference

* assignment

* block, `if`, `while`, `for`, `return`

* first order functions
:::
:::col
{lbl}[Forbidden]

* class, pointer, vector, function types

* `new`, `delete`

* `this`, field access, dereference, indexing

* method call, class template

* lambda, `std::function`
:::
::::

# §25.2 The checker runs

```lean (name := fragCheck)
def mdc : String :=
  "int mdc(int a, int b) {
    while (b != 0) { int t = b; b = a % b; a = t; }
    return a;
  }
  int main() { int x = mdc(48, 18); int& y = x; y = y + 1; return y; }"

#eval (parseProgram mdc).map (fragment .imperative)
```
```leanOutput fragCheck
Except.ok (Except.ok ())
```

```lean (name := fragReject)
def comClasse : String :=
  "class C { public: int v; };
   int main() { C* c = new C(); return c->v; }"

#eval (parseProgram comClasse).map (fragment .imperative)
```
```leanOutput fragReject
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class C" })
```

# §25.3 What the restriction buys

* *Every value in σ is basic.* No rule of the fragment produces a location, an object, a vector or a closure.

* *The store is a stack.* A location enters at a declaration or a parameter binding and leaves at the exit of its scope, in reverse order.

* *A dangling location is unreachable.* An expression reaches a location only through ρ, and ρ binds a name only while it lives.

* Three of the eight `error` results disappear, the double `delete`, the access after `delete` and the `delete` through a base pointer.

# §25.3 The price, and the shape of the argument

* Without the heap, *no data structure outlives the function that built it*. The vector is out because it needs `new`.

* That is why the object oriented fragment exists, and why C has pointers.

* The shape of every claim of this unit. The fragment is smaller, so *fewer rules apply*, so *more can be said*.

# §25.4 Control

* Sequence, selection, repetition. `While-T` recurs on its own conclusion.

* A program is read as a *sequence of state changes in time*, and its meaning is the final store.

* Lecture 27 reads the same computation as a *term whose value does not depend on time*. Same ρ, same σ, same rules.

# Summary

* A *fragment* is a set of forbidden constructions, a predicate over the abstract syntax, checked after parsing and typing.

* The *imperative fragment* keeps the basic types, the variables, the assignment, the commands and the first order functions.

* It buys a *stack discipline* for σ, only basic values, and no dangling location.

* It costs the heap, so no data structure outlives its function.

* Forbid this, gain that. That exchange is the whole unit.

Exercises: see the [lecture notes](../en/Lecture-25___-The-Imperative-Paradigm/).

```lean -show
end Slides25
```
