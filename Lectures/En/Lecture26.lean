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

#doc (Manual) "Lecture 26: The Object Oriented Paradigm" =>

%%%
tag := "lecture-26"
%%%

```lean -show
namespace Lecture26
open CoreCpp
```

The object oriented fragment is the imperative one with the heap and the class. The lecture gives the fragment, says what the heap costs in the statements of {secref}[lecture-25] and what encapsulation and dispatch buy in return, and models the case study of the unit with classes. The reading it proposes is that a program of this paradigm is a set of objects that hold state and answer messages, and that the two organising principles, encapsulation and dispatch, are both about *who may know what*.

*This lecture is also available as [presentation slides](../slides/lecture-26.en.html).*

# The Fragment

%%%
tag := "oo-fragment"
%%%

The object oriented fragment admits everything the imperative one admits, and adds the class with its fields, methods, constructor and destructor, `this`, single inheritance, `virtual`, `override`, dispatch, subsumption, `new`, `delete`, pointers, vectors, overloading, operator members, class templates and namespaces. It forbids three constructions, the lambda, the type `std::function` and the call through a function value.

The three forbidden ones are the same construction seen from three sides, the function as a value. A language of this paradigm packages behaviour in an object, not in a value of function type, so the fragment asks a program to say with a `virtual` method what it might otherwise say with a lambda. That is the point of the restriction, and {secref}[dispatch-vs-closure] returns to it.

```lean (name := ooCheck)
def conta : String :=
  "class Conta {
   public:
     int saldo;
     virtual int taxa() { return 2; }
     void deposita(int v) { saldo = saldo + v; }
     virtual ~Conta() { }
   };
   class Poupanca : public Conta { public: int taxa() override { return 0; } };
   int main() {
     Conta* c = new Conta(); c->deposita(10);
     Conta* p = new Poupanca(); p->deposita(10);
     int r = c->taxa() + p->taxa() + c->saldo;
     delete c; delete p; return r;
   }"

#eval (parseProgram conta).map (fragment .oo)
```
```leanOutput ooCheck
Except.ok (Except.ok ())
```

The same program lies outside the imperative fragment, at its first class.

```lean (name := ooNotImp)
#eval (parseProgram conta).map (fragment .imperative)
```
```leanOutput ooNotImp
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class Conta" })
```

And a program that returns a lambda lies outside the object oriented one, at the type that carries it.

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

# What the Heap Costs

%%%
tag := "heap"
%%%

{secref}[lecture-25] claimed three things for the imperative fragment, and the heap costs two of them.

*Values in σ are no longer basic.* An object is a record of locations with a class tag, a vector is a record of locations, and a pointer is a location. All three are values of the fragment, so the store now holds structure as well as data.

*The store no longer follows a stack discipline.* The rule `New` allocates the locations of the fields, and nothing releases them at the exit of the block. They leave σ at a `delete`, which may be anywhere or nowhere, so the lifetime of an object is decided by the program and not by the shape of its text. That is precisely what the paradigm wanted, because an object that could not outlive the function that built it would be of little use.

*A dangling location becomes reachable.* With the store free of the stack discipline, a program may hold a pointer to an object it has deleted. Core C++ answers with `error` rather than with undefined behaviour, and the three ways in are the double `delete`, the access after `delete` and the `delete` through a base pointer without a virtual destructor, all of {secref}[lecture-19].

One statement survives, and it is the one that makes the paradigm workable.

*Every location allocated by `new` is reached in one of two ways*, through a pointer held in a variable, a field or a parameter, or through `this` inside a method. There is no third channel, because the fragment has no closure to capture a pointer and carry it elsewhere, and no global variable to park it in. Reasoning about which part of a program can touch an object therefore reduces to following the pointers, which is what makes encapsulation mean anything.

# Encapsulation and Dispatch

%%%
tag := "principles"
%%%

The two organising principles of the paradigm are both restrictions on knowledge, and both are typing rules.

*Encapsulation* says that the representation of an object is known only inside its class. In Core C++ that is the visibility rule of {secref}[lecture-17], a private member is reachable only from a member body of the class that declares it, checked in Γ before the program runs. The class is therefore an abstract data type whose public members are the signature and whose private fields are the representation, and a caller that respects the signature cannot be broken by a change of representation.

*Dispatch* says that the code a call runs is known only at run time, by the class tag of the receiver. In Core C++ that is the rule `Dispatch` of {secref}[lecture-19], and its condition is the `virtual` marker. The caller therefore knows the signature and not the code, which is the other half of the same idea, and the two together are what lets a program be extended by a class its author never saw.

The case study of the unit shows both. The criterion of the sum is a `virtual` method, so the derived class chooses it, and the accumulator is a field, so no caller can reach it except through `junta` and `total`.

```lean (name := caseOo)
def caseOo : String :=
  "class Somador {
   public:
     int acc;
     virtual bool aceita(int i) { return true; }
     void junta(int i) { if (aceita(i)) { acc = acc + i; } }
     int total() { return acc; }
     virtual ~Somador() { }
   };
   class SomadorPar : public Somador {
   public:
     bool aceita(int i) override { return i % 2 == 0; }
   };
   int main() {
     Somador* s = new SomadorPar();
     for (int i = 1; i <= 10; i = i + 1) { s->junta(i); }
     int r = s->total();
     delete s;
     return r;
   }"

#eval (parseProgram caseOo).map fun p => (fragment .oo p, run p)
```
```leanOutput caseOo
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

The method `junta` is declared once, in the base, and calls `aceita`, which the derived class redefines. The call inside `junta` is dispatched, so `junta` runs the criterion of the object it was called on, without knowing which. Extending the program with a third criterion is one new class and no change to `junta`.

# Dispatch and the Closure

%%%
tag := "dispatch-vs-closure"
%%%

{secref}[lecture-27] writes the same case study with a lambda in place of the derived class, and the two are worth setting side by side, because they solve one problem twice.

A `virtual` method and a closure both package behaviour and carry it to a place that does not know what it is. The difference is what they carry it with. The method travels inside an object, together with its state, and is selected by a tag; the closure travels alone, together with the copies it captured, and is selected by being the value it is. The object oriented fragment keeps the first and forbids the second, the functional fragment does the reverse, and Core C++ has both, which is why the two examples of the case study run in the same interpreter.

The exchange is visible in the tables of {secref}[lecture-29]. Dispatch puts the extension point in the type hierarchy, so a new behaviour is a new class and the call sites do not change. A closure puts the extension point in the argument list, so a new behaviour is a new value and the type does not change. Neither is better; they distribute the same freedom differently.

# Exercises

%%%
tag := "exercises-26"
%%%

{exercise "exr-oo-third"}[] Extend the case study with a third criterion, the multiples of three, and confirm that `junta` does not change. Say which line of the rule `Dispatch` decides the call.

{exercise "exr-oo-leak"}[] Write a program of the object oriented fragment that allocates an object and never deletes it, and one that deletes it twice. Say what each returns, and which of the three `error` results of `delete` the second reaches.

{exercise "exr-oo-private"}[] Make `acc` private in the case study and add the method the program then needs. Explain, in terms of Γ, why the change does not affect `main`.

{exercise "exr-oo-reach"}[] {secref}[heap] claims that every heap location is reached through a pointer or through `this`. Give the argument for the rule `Field` and for the rule `MethodCall`, and say where a closure would break it.

{exercise "exr-oo-vector"}[] Rewrite the case study so that the numbers come from a `std::vector<int>` built with `new`, and say which locations the program leaves in σ at the end and why.

{exercise "exr-oo-static"}[] Remove the `virtual` from `aceita` and run the program again. Explain the result from the rule that chooses the method, and say what the type checker would say if `override` were left in place.

```lean -show
end Lecture26
```
