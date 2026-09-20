/-
Slides of Lecture 17. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Abstract Data Types" =>

Signature and representation, visibility as a typing rule, the class table

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-17___-Abstract-Data-Types/)

{cite}[B. Liskov and S. Zilles, *Programming with Abstract Data Types*, SIGPLAN Notices 9(4), 1974.]

```lean -show
namespace Slides17
open CoreCpp
```

# §17.1 Signature and representation

* A stack is known by four operations. Create, push, pop, empty.

* The operations are the *signature*. The vector and the counter are the *representation*.

* Whoever uses the type depends only on the signature, so the representation may change without touching the clients.

* The signature is a *contract*, the representation a private decision.

{cite}[D. L. Parnas, *On the Criteria To Be Used in Decomposing Systems into Modules*, CACM 15(12), 1972.]

# §17.1 A stack in Core C++

```lean (name := stack)
def stack : String :=
  "class Pilha {
  private:
    std::vector<int>* itens;
    int topo;
  public:
    Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
    void empilha(int x) { (*itens)[topo] = x; topo = topo + 1; }
    int desempilha() { topo = topo - 1; return (*itens)[topo]; }
    bool vazia() { return topo == 0; }
  };
  int main() {
    Pilha* p = new Pilha(8);
    p->empilha(1);
    p->empilha(41);
    return p->desempilha() + p->desempilha();
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

# §17.2 Visibility is a typing rule

```lean (name := peek)
def peek : String :=
  "class Pilha {
  private:
    std::vector<int>* itens;
    int topo;
  public:
    Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
  };
  int main() { Pilha* p = new Pilha(8); return p->topo; }"

#eval (parseProgram peek).map check
```
```leanOutput peek
Except.ok (Except.error (CoreCpp.TypeError.privateMember "Pilha" "topo"))
```

* The contract is enforced *before the program runs*.

# §17.2 The rule Visible

```tree
C has τ f declared in K    f public or Γ(this) = K*
──────────────────────────────────────────────────── (Visible)
```

* Inside a member body Γ binds `this` to $`C*`. The *current class* is the class of `this`.

* Outside every class there is no `this`, so only public members are visible.

* A derived class does not see the private members of its base. Same rule as C++.

* Core C++ keeps `public` and `private` only. No `protected`, `friend` or `static`.

# §17.3 The class table

:::table +header
*
  * Question
  * Answer
*
  * chain of a class
  * the class, its base, the base of the base, up to the root
*
  * fields of an object
  * every field of the chain, root base first
*
  * method of a class
  * the nearest declaration of that name in the chain
*
  * does $`D` derive from $`B`
  * $`B` is in the chain of $`D`
*
  * virtual destructor
  * some class of the chain declares one
:::

* The type checker, `new`, `delete` and dispatch all consult the same table.

# §17.4 A well formed class

```tree
B exists and the chain of C has no cycle
fields storable, well formed, new in the chain
members with distinct names
each redefined method is virtual in the base, marked override, same signature
the constructor of B, if any, takes no parameters
[this ↦ C*, x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'   for every member body
────────────────────────────────────────────────────────────────── (T-Class)
⊢ class C : public B { … }
```

* Bodies are checked under `this ↦ C*` and the parameters. Constructors and destructors return `void`.

* No initialiser lists, so the base constructor takes no parameters.

# §17.5 Representation invariants

* A property every operation preserves. For the stack, `topo` stays in bounds and the values below it are the ones pushed and not popped.

* Visibility makes the invariant *provable*. Only the methods write the fields, so checking each method suffices.

* A client that pushes nine values on a stack of eight breaks the contract. In C++ the write is undefined. In Core C++ it is `error`, by `LocIndex`.

* A stack that checks its bounds keeps the invariant by itself.

# Summary

* An *abstract data type* is a signature over a hidden representation. In Core C++, a `class` with `public` and `private` sections.

* *Visibility* is a typing rule. A private member of $`K` is visible only when `this` has class $`K`.

* The *class table* answers every question about chains, fields, methods and destructors.

* `T-Class` checks the shape of the class and every member body under `this ↦ C*`.

* Visibility is what makes a *representation invariant* provable by checking the methods alone.

Exercises: see the [lecture notes](../en/Lecture-17___-Abstract-Data-Types/).

```lean -show
end Slides17
```
