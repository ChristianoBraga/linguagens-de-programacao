/-
Slides of Lecture 20. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Object Orientation" =>

Namespaces, the object oriented paradigm, separate compilation and development processes

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-20___-Object-Orientation/)

```lean -show
namespace Slides20
open CoreCpp
```

# §20.1 Namespaces

```lean (name := ns)
def ns : String :=
  "namespace Banco {
    class Conta {
    private:
      int saldo;
    public:
      Conta(int inicial) { saldo = inicial; }
      void deposita(int v) { saldo = saldo + v; }
      int consulta() { return saldo; }
    };
  }
  int main() {
    Banco::Conta* c = new Banco::Conta(100);
    c->deposita(20);
    return c->consulta();
  }"

#eval (parseProgram ns).map run
```
```leanOutput ns
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

```lean (name := nsNames)
#eval (parseProgram ns).map fun p => p.classes.map (·.name)
```
```leanOutput nsNames
Except.ok ["Banco::Conta"]
```

* Flattened by the parser. No rule of typing or evaluation.

# §20.2 The paradigm in the rules

* *Encapsulation*. `Visible` confines the representation to the methods.

* *Identity and state*. An object is a record in σ, reached by pointers. Two pointers to one location name one object.

* *Substitutability*. `Subsumption` lets a client of `Forma*` receive any derived class, including ones written later.

* *Late binding*. The `virtual` premise of `MethodCall` decides the method by the object, at every call.

{cite}[B. Meyer, *Object-Oriented Software Construction*, 2nd ed., Prentice Hall, 1997.]

# §20.2 Abstract data type or object

* An abstract data type has *one* representation, and its operations see it, also on other values of the type. The stack compares two stacks by reading both.

* An object exposes only its *signature*, even to objects of its own class. Two objects may hide different representations behind one signature.

* Core C++ offers both. The difference is one of design.

{cite}[W. R. Cook, *On Understanding Data Abstraction, Revisited*, OOPSLA 2009.]

# §20.3 Separate compilation

```
// pilha.hh                          // pilha.cpp
class Pilha {                         #include "pilha.hh"
private:                              Pilha::Pilha(int n) { … }
  std::vector<int>* itens;            void Pilha::empilha(int x) { … }
  int topo;                           int Pilha::desempilha() { … }
public:                               bool Pilha::vazia() { … }
  Pilha(int n);
  void empilha(int x);
  int desempilha();
  bool vazia();
};
```

* The header is the signature, the source the operations. A change to the source relinks the clients, it does not recompile them.

* Needs `#include` and methods defined outside the class. Core C++ has neither. No new rule.

# §20.4 Development processes

* The abstract data type is the *unit of work*. Specified, implemented, tested and replaced on its own.

* *Sequential*. Requirements, design, code, test, with the warning that one pass rarely works.

* *Iterative*. Short cycles, each delivering a part. Signatures let a part exist before the rest.

* *Test driven*. The test of a signature before its implementation. The test is a client of the type.

* Visibility is why the contract can be trusted. A test of the signature tests everything a client can do.

{cite}[W. W. Royce, *Managing the Development of Large Software Systems*, IEEE WESCON, 1970. K. Beck, *Test-Driven Development, By Example*, Addison-Wesley, 2002.]

# §20.5 The fragment of Unit V

:::table +header
*
  * Construction
  * Typing
  * Evaluation
*
  * class with sections, base, constructor, destructor
  * `T-Class`
  * the class table
*
  * private member
  * `Visible`
  * none
*
  * `this`, unqualified member
  * `T-This`, `T-VarField`
  * `This`, `LocVarField`
*
  * `new C(args)`
  * `T-New`
  * `New`
*
  * `e->m(args)`
  * `T-MethodArrow`
  * `MethodCall`, `Member`
*
  * `D* ≈ B*`
  * `Subsumption`
  * none
*
  * `delete e`
  * `T-Delete`
  * `Delete`, `DeleteVec`, `DeleteNull`
:::

# Summary

* A `namespace` groups classes under `N::`, flattened by the parser.

* The object oriented paradigm is readable in the rules. Encapsulation, identity, substitutability, late binding.

* An abstract data type and an object differ in where the operations live.

* Separate compilation is the C++ idiom for the abstract data type at the scale of files, with no new rule.

* Development processes organise work around signatures, and visibility is what makes the contract trustworthy.

Exercises: see the [lecture notes](../en/Lecture-20___-Object-Orientation/).

```lean -show
end Slides20
```
