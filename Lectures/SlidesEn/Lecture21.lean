/-
Slides of Lecture 21. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Overloading" =>

One name, several declarations, and the argument types choose

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-21___-Overloading/)

```lean -show
namespace Slides21
open CoreCpp
```

# §21.1 One name, several declarations

* A name denotes an *overload set*, and a call picks one member of it by the types of the arguments.

* The choice is made in Γ, by the type checker, and the program that runs holds one call to one function.

* Overloading *costs nothing at run time*.

```lean (name := overload)
def overload : String :=
  "int twice(int n) { return 2 * n; }
  bool twice(bool b) { return b; }
  int twice(int a, int b) { return 2 * (a + b); }
  int main() {
    int x = twice(21);
    int y = twice(1, 1);
    return twice(false) ? 0 : x + y;
  }"

#eval (parseProgram overload).map run
```
```leanOutput overload
Except.ok (Except.ok (CoreCpp.Val.int 46))
```

# §21.2 The rule that selects a candidate

```tree
A = the candidates of cand(f, k) that accept e₁, …, eₖ
A has one element whose parameters are exactly the types of the arguments, or A is a singleton
────────────────────────────────────────────────────────────────────────────── (T-Overload)
the call of f selects that candidate
```

* A *accepts* means each argument by value is acceptable at its parameter type, and each argument of a reference parameter denotes a location of that type.

* A empty, the error of the single candidate of that arity. A a singleton, that one. Two or more, the *exact* one wins.

* No exact one, the call is *ambiguous*. Core C++ does not rank conversion sequences.

# §21.2 Ambiguity through subsumption

::::cols
:::col
{lbl}[Ambiguous in Core C++]

```lean (name := ambiguous)
def ambiguous : String :=
  "class A { public: int a; };
  class B : public A { public: int b; };
  class C : public B { public: int c; };
  int f(A* x) { return 1; }
  int f(B* x) { return 2; }
  int main() { C* z = new C(); return f(z); }"

#eval (parseProgram ambiguous).map check
```
```leanOutput ambiguous
Except.ok (Except.error (CoreCpp.TypeError.ambiguousCall "f"))
```
:::
:::col
{lbl}[Exact, and accepted]

```lean (name := exact)
def exact : String :=
  "class A { public: int a; };
  class B : public A { public: int b; };
  int f(A* x) { return 1; }
  int f(B* x) { return 2; }
  int main() { B* z = new B(); return f(z); }"

#eval (parseProgram exact).map run
```
```leanOutput exact
Except.ok (Except.ok (CoreCpp.Val.int 2))
```
:::
::::

* C++ accepts the left one and runs `f(B*)`, by a page of ranking rules.

# §21.3 When two declarations may share a name

```tree
arities differ, or ∃ i. pᵢ ≠ qᵢ and neither pᵢ nor qᵢ is std::function
──────────────────────────────────────────────────────────────────── (Distinguishable)
the two declarations are overloads
```

* A lambda has *no type of its own*, it is checked against the expected `std::function`.

* Choosing a candidate would need the type of the lambda, and typing the lambda would need the candidate.

```lean (name := indistinguishable)
def indistinguishable : String :=
  "int g(std::function<int(int)> h) { return h(1); }
  int g(std::function<bool(bool)> h) { return 0; }
  int main() { return 0; }"

#eval (parseProgram indistinguishable).map check
```
```leanOutput indistinguishable
Except.ok (Except.error (CoreCpp.TypeError.indistinguishable "g"))
```

# §21.4 Methods overload like functions

* The overload set of a method name is the set along the *chain*, one per signature.

* Same signature as a base method, it is a *redefinition*, and needs `virtual` and `override`.

* Different signature, it is *another overload*, and needs nothing.

* C++ *hides* every base `m` behind a derived `m`. The subset takes the union of the chain instead.

```lean (name := methodOverload)
def methodOverload : String :=
  "class Account {
  private:
    int balance;
  public:
    Account(int s) { this->balance = s; }
    int deposit(int v) { balance = balance + v; return balance; }
    int deposit(int v, int rate) { return deposit(v - rate); }
    int value() { return balance; }
  };
  int main() {
    Account* c = new Account(100);
    c->deposit(50);
    c->deposit(20, 5);
    return c->value();
  }"

#eval (parseProgram methodOverload).map run
```
```leanOutput methodOverload
Except.ok (Except.ok (CoreCpp.Val.int 165))
```

# §21.5 Operators are members

```tree
Γ ⊢ e₁ : C    C has operator⊕ visible from Γ    Γ ⊢ e₁.operator⊕(e₂) : τ
──────────────────────────────────────────────────────────────────── (T-OpBin)
Γ ⊢ e₁ ⊕ e₂ : τ
```

* The *left operand decides*, so `1 + 2` keeps its meaning and no class may change it.

* The parameter is `Point& o`, because an object is never copied. The result is `Point*`, for the same reason.

* Arithmetic, comparison and indexing. Not `&&` and `||`, which short circuit.

# §21.5 The infix form is a method call

```lean (name := operatorPlus)
def operatorPlus : String :=
  "class Point {
  public:
    int x;
    int y;
    Point* operator+(Point& o) {
      Point* r = new Point();
      r->x = x + o.x;
      r->y = y + o.y;
      return r;
    }
  };
  int main() {
    Point* a = new Point();
    a->x = 1; a->y = 4;
    Point* b = new Point();
    b->x = 2; b->y = 3;
    Point* c = *a + *b;
    return c->x + c->y;
  }"

#eval (parseProgram operatorPlus).map run
```
```leanOutput operatorPlus
Except.ok (Except.ok (CoreCpp.Val.int 10))
```

* The type checker *rewrites* the infix form into the call of the member. Visibility, resolution and dispatch then apply as usual.

# Summary

* A name denotes an *overload set*, and the argument types select one candidate, in Γ, at no run time cost.

* *T-Overload*. The candidates that accept, then the exact one, or a single one, or ambiguity.

* Two declarations of one name are *distinguishable* by arity or by a parameter that is not a `std::function`.

* Methods overload along the *chain*, and a different signature is an overload, not a redefinition.

* An operator on an object is a *member call*, which the type checker writes, and the derivation shows `MethodCall`.

Exercises: see the [lecture notes](../en/Lecture-21___-Overloading/).

```lean -show
end Slides21
```
