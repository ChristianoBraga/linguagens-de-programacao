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

#doc (Manual) "Lecture 20: Object Orientation" =>

%%%
tag := "lecture-20"
%%%

```lean -show
namespace Lecture20
open CoreCpp
```

This lecture closes Unit V. It looks at object orientation as a way of organising a program around the constructions of the three previous lectures, at the namespace as the grouping of classes, at separate compilation as the C++ idiom for the abstract data type, and at the development processes that the syllabus asks the course to discuss. The last topic has no rules. The lecture ends with the fragment of Core C++ implemented up to this unit.

*This lecture is also available as [presentation slides](../slides/lecture-20.en.html).*

# Namespaces

%%%
tag := "namespaces"
%%%

A program with many classes needs a way to group them and to keep their names apart. A `namespace N { … }` groups classes under the prefix `N::`, and a client names them by their qualified name.

```lean (name := ns)
def ns : String :=
  "namespace Bank {
    class Account {
    private:
      int balance;
    public:
      Account(int initial) { balance = initial; }
      void deposit(int v) { balance = balance + v; }
      int query() { return balance; }
    };
  }
  int main() {
    Bank::Account* c = new Bank::Account(100);
    c->deposit(20);
    return c->query();
  }"

#eval (parseProgram ns).map run
```
```leanOutput ns
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

The namespace adds no rule of typing or of evaluation. The parser flattens it, so the class table receives a class named `Bank::Account` and every rule works on that name.

```lean (name := nsNames)
#eval (parseProgram ns).map fun p => p.classes.map (·.name)
```
```leanOutput nsNames
Except.ok ["Bank::Account"]
```

Inside the namespace an unqualified class name denotes the class of the namespace, so the constructor `Account(int)` and a field of type `Account*` need no prefix there. Core C++ keeps only this much of the C++ namespace. There is no `using`, no functions or variables inside a namespace, and no way to reach a class of an enclosing scope from inside a namespace but by its qualified name.{fnref}[nested]

:::footnotes

{fnAnchor "nested"}[] Namespaces nest, and a class declared in `namespace A { namespace B { … } }` is named `A::B::C`. The rule for unqualified names inside a namespace resolves them to the innermost namespace, `A::B::C`, and a class of `A` is reached from inside `B` as `A::C`. C++ resolves an unqualified name by searching the enclosing scopes outwards, and Core C++ simplifies that search to one scope.

:::

# Object Orientation

%%%
tag := "oo"
%%%

The constructions of Unit V, classes with visibility, objects with identity in σ, constructors, dispatch and inheritance, are the vocabulary of the *object oriented* paradigm, one of the four of {secref}[lecture-1]. The paradigm organises a program as a set of objects that hold state and answer to method calls, and lets a client work with an object through a base type while the object's own class decides what each call does. What the paradigm favours can be read off the rules.

*Encapsulation.* The rule `Visible` of {secref}[lecture-17] confines the representation to the methods. A client sees a signature, and a representation invariant is preserved by checking the methods alone.

*Identity and state.* An object is a record of locations in σ, {secref}[lecture-6], reached through pointers. Two pointers to the same location name the same object, changes through one are seen through the other, and an object outlives the block that created it. This is the model of a mutable entity with an identity, the opposite of the value semantics of Unit II, where two equal integers are indistinguishable.

*Substitutability.* The rule `Subsumption` of {secref}[lecture-19] lets a client written against `Shape*` receive a `Square*`. Any operation of the signature of `Shape` applies to the object, so the client works unchanged for every class that derives from `Shape`, including classes written after the client.{margin}[B. Meyer, *Object-Oriented Software Construction*, 2nd ed., Prentice Hall, 1997, chapters 14 and 16.]

*Late binding.* The premise on `virtual` in `MethodCall` decides the method by the object, not by the pointer. A client that calls `f->area()` need not know which shape it holds, and the choice is made at run time, at every call.

Cook observes that an abstract data type and an object differ in where the operations live.{margin}[W. R. Cook, *On Understanding Data Abstraction, Revisited*, Proceedings of OOPSLA 2009, pp. 557 to 572.] An abstract data type has one representation and operations that see it, like the stack of {secref}[lecture-17], whose methods read the vector and the counter of the receiver and of any other stack passed to them. An object exposes only its signature, even to other objects of the same class, so two objects may have different representations behind the same signature, as `Square` and a hypothetical `Circulo` behind `Shape`. Core C++ offers both, and the difference is one of design, not of language.

# Separate Compilation

%%%
tag := "separate"
%%%

C++ programs of any size are split into files. A *header* `.hh` declares a class, its fields and the signatures of its methods, and a *source* `.cpp` defines the methods with the qualified syntax `Stack::push`. Clients include the header and never see the source. The compiler translates each source into an object file, and the linker joins them into a program.

```
// stack.hh
class Stack {
private:
  std::vector<int>* items;
  int top;
public:
  Stack(int n);
  void push(int x);
  int pop();
  bool empty();
};

// stack.cpp
#include "stack.hh"
Stack::Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
void Stack::push(int x) { (*items)[top] = x; top = top + 1; }
int Stack::pop() { top = top - 1; return (*items)[top]; }
bool Stack::empty() { return top == 0; }
```

Separate compilation is the C++ idiom for the abstract data type at the scale of files. The header is the signature, the source is the representation of the operations, and a change to the source does not force the clients to be recompiled, only relinked. It rests on the preprocessor, `#include`, and on the definition of methods outside the class, and Core C++ has neither. The design keeps a program as one file and one translation unit, because the idiom adds no rule of typing or of evaluation to the ones of {secref}[lecture-17] and {secref}[lecture-18]. The header still exposes the private fields, since the compiler needs the size of an object, and the fully opaque type needs the pointer to implementation idiom, a class whose only field is a pointer to a private class defined in the source.

# Development Processes

%%%
tag := "processes"
%%%

The syllabus lists object orientation and development processes together, and the connection is the abstract data type. A signature that is fixed before its representation is a unit of work that can be specified, implemented, tested and replaced on its own, and every development process since Parnas has organised work around such units.

A *sequential* process fixes the requirements, then the design, then writes the code and tests it, each phase feeding the next. Royce described that sequence and warned, in the same paper, that a single pass rarely works and that the design must be revisited after testing.{margin}[W. W. Royce, *Managing the Development of Large Software Systems*, Proceedings of IEEE WESCON, 1970, pp. 1 to 9.] An *iterative* process builds the program in short cycles, each one delivering working software for a part of the requirements, and the signatures of the classes are what allows a part to be delivered before the rest exists. *Test driven* development writes the test of a signature before its implementation, and the test is a client of the abstract data type.{margin}[K. Beck, *Test-Driven Development, By Example*, Addison-Wesley, 2002.]

In every process the class is the unit that changes hands. Its signature is what the team agrees on, its representation is what one developer owns, and its tests are what tells both that the contract holds. The rules of this unit are the reason the contract can be trusted. Visibility makes the representation unreachable, so a test of the signature tests everything a client can do.

# The Fragment of Unit V

%%%
tag := "fragment-20"
%%%

{numref}[tbl-fragment-20] lists the constructions Unit V added to Core C++, with the rules of each. The specification of the fragment is `spec-ud5.md`, and the blueprint chapter on encapsulation points each rule to the Lean function that implements it.

:::table +header
*
  * Construction
  * Typing
  * Evaluation
*
  * class with sections, base, constructor and destructor
  * `T-Class`
  * the class table
*
  * private member
  * `Visible`
  * none, visibility is static
*
  * `this`, unqualified member
  * `T-This`, `T-VarField`
  * `This`, `LocVarField`
*
  * `new C(args)`
  * `T-New`
  * `New`, the constructors from the root down
*
  * `e->m(args)`, `e.m(args)`
  * `T-MethodArrow`, `T-Method`
  * `MethodCall`, `Member`, dispatch by the tag when virtual
*
  * `D* ≈ B*`
  * `Subsumption`
  * none, the tag never changes
*
  * `delete e`
  * `T-Delete`, `T-DeleteVec`
  * `Delete`, `DeleteVec`, `DeleteNull`, the destructors from the tag up
*
  * `namespace N`
  * none, flattened by the parser
  * none
:::

{tabcap "tbl-fragment-20"}[The constructions of Unit V and their rules.]

Three properties of the fragment deserve record. Every object still lives in σ from `new` to `delete` or the end of the program, and is never copied, so the model of Unit II stands. Static and dynamic dispatch agree on every non virtual method, by the restriction on redefinition. The three undefined behaviours of C++17 around `delete`, the double `delete`, the access after `delete` and the `delete` through a base pointer without a virtual destructor, are `error` in Core C++, by the rules of {secref}[lecture-19].

# Exercises

%%%
tag := "exercises-20"
%%%

{exercise "exr-ns-nested"}[] Write two namespaces, one nested in the other, each with a class, and a `main` that creates one object of each. Print the class table with `Program.classes` and explain the names.

{exercise "exr-adt-vs-object"}[] Add to the stack of {secref}[lecture-17] a method `igual(Stack* outra)` that compares two stacks by reading the fields of `outra`. Explain, with Cook's distinction, why this method is possible for an abstract data type and would not be for an object known only by its signature.

{exercise "exr-substitution"}[] Write a function that receives a `Shape*` and returns twice its area, and call it with a `Square*` and with a `Shape*`. Explain, by `Subsumption` and `MethodCall`, why one function serves both.

{exercise "exr-header"}[] Split the program of {secref}[namespaces] into a header and a source in real C++, compile them with `g++` and describe which change to the source forces the client to be recompiled and which does not.

{exercise "exr-tdd"}[] Write, before implementing it, a `main` that tests a class `Conjunto` with the operations insert, contains and size over a vector, with the expected result in the return value. Then implement the class until the test passes under the interpreter and under `g++`.

{exercise "exr-fragment-review"}[] For each row of {numref}[tbl-fragment-20], write a program of at most six lines accepted by the type checker and one rejected, and name the rule that rejects it.

```lean -show
end Lecture20
```
