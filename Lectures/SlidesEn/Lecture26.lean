/-
Slides of Lecture 26. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "The Object Oriented Paradigm" =>

The fragment with the heap and the class, encapsulation and dispatch

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-26___-The-Object-Oriented-Paradigm/)

```lean -show
namespace Slides26
open CoreCpp
```

# §26.1 The fragment

* The imperative fragment *plus* the class, methods, constructors, destructors, `this`, inheritance, `virtual`, dispatch, `new`, `delete`, pointers, vectors, overloading, templates, namespaces.

* It forbids three constructions, the *lambda*, the type `std::function` and the call through a function value.

* The three are the same thing from three sides, *the function as a value*. This paradigm packages behaviour in an *object*.

```lean (name := ooNotFn)
def comLambda : String :=
  "std::function<int()> f() {
     return [=]() -> int { return 1; };
   }
   int main() { return f()(); }"

#eval (parseProgram comLambda).map (fragment .oo)
```
```leanOutput ooNotFn
Except.ok (Except.error { frag := CoreCpp.Frag.oo, what := "function type", site := "function f" })
```

# §26.2 What the heap costs

* *Values in σ are no longer basic.* Objects, vectors and pointers live there.

* *The store is no longer a stack.* `New` allocates, nothing releases at block exit, `delete` may be anywhere or nowhere.

* *A dangling location becomes reachable.* Three `error` results answer for it, instead of undefined behaviour.

* *One statement survives.* Every heap location is reached through a *pointer* or through `this`. There is no third channel, because the fragment has no closure and no global.

# §26.3 Encapsulation and dispatch

::::cols
:::col
{lbl}[Encapsulation]

* The representation is known only inside the class.

* A typing rule, checked in Γ *before* the program runs.

* The class is an abstract data type, public signature and private representation.
:::
:::col
{lbl}[Dispatch]

* The code a call runs is known only at run time, by the *class tag*.

* The rule `Dispatch`, conditioned on `virtual`.

* The caller knows the signature, not the code.
:::
::::

* Both are restrictions on *who may know what*, and together they let a program be extended by a class its author never saw.

# §26.3 The case study

```lean (name := caseOo)
def caseOo : String :=
  "class Adder {
   public:
     int acc;
     virtual bool accepts(int i) { return true; }
     void add(int i) { if (accepts(i)) { acc = acc + i; } }
     int total() { return acc; }
     virtual ~Adder() { }
   };
   class EvenAdder : public Adder {
   public:
     bool accepts(int i) override { return i % 2 == 0; }
   };
   int main() {
     Adder* s = new EvenAdder();
     for (int i = 1; i <= 10; i = i + 1) { s->add(i); }
     int r = s->total();
     delete s;
     return r;
   }"

#eval (parseProgram caseOo).map fun p => (fragment .oo p, run p)
```
```leanOutput caseOo
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* `add` is declared once and calls `accepts`, which the derived class redefines. A third criterion is *one new class and no change to junta*.

# §26.4 Dispatch and the closure

* Both package behaviour and carry it where it is not known.

* The *method* travels inside an object, with its state, selected by a tag. The *closure* travels alone, with its copies, selected by being that value.

* Dispatch puts the extension point in the *type hierarchy*. A closure puts it in the *argument list*.

* Neither is better. They distribute the same freedom differently, and Core C++ has both.

# Summary

* The object oriented fragment is the imperative one *with the heap and the class*, and without the function as a value.

* The heap costs the stack discipline and makes a dangling location reachable, answered by three `error` results.

* What survives is that every heap location is reached by a *pointer* or by `this`.

* *Encapsulation* and *dispatch* are both typing rules, and both are about who may know what.

* The extension point of the paradigm is the *class hierarchy*.

Exercises: see the [lecture notes](../en/Lecture-26___-The-Object-Oriented-Paradigm/).

```lean -show
end Slides26
```
