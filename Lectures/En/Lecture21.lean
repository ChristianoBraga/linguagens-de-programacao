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

#doc (Manual) "Lecture 21: Overloading" =>

%%%
tag := "lecture-21"
%%%

```lean -show
namespace Lecture21
open CoreCpp
```

This lecture opens Unit VI with the first form of polymorphism a language offers, *overloading*, in which one name stands for several declarations and the types of the arguments choose between them. The lecture gives the rule that selects a candidate, says when two declarations of one name are allowed to live together, and ends with the operators, which in C++ are members with a name of their own. The choice happens in Γ, before the program runs, so overloading costs nothing at run time.

*This lecture is also available as [presentation slides](../slides/lecture-21.en.html).*

# One Name, Several Declarations

%%%
tag := "overload-set"
%%%

A program may declare several functions with one name, provided they take different arguments. The name then denotes an *overload set*, and a call picks one member of the set by the types of its arguments. The choice is made by the type checker, and the program that runs holds one call to one function, as if the programmer had written three distinct names.

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

The three declarations of `twice` differ in the number of arguments, in the first case, and in the type of the argument, in the second. Each call in `main` reaches one of them. Nothing in the values distinguishes the calls at run time, and the interpreter is told which function to enter by the type checker, which writes the *signature* of the chosen declaration into the tree.

The usefulness is a matter of naming. Without overloading, a library that prints an `int`, a `bool` and a pointer offers three names, `imprimeInt`, `imprimeBool`, `imprimePonteiro`, and the reader must remember which one to write. With overloading it offers `imprime`, and the argument decides. The counterpart is that the reader of a call must know the types of the arguments to know which declaration runs, which is why a language that overloads should also keep the candidates few and distinct.

# The Rule That Selects a Candidate

%%%
tag := "resolution"
%%%

Let `cand(f, k)` be the declarations of `f` with `k` parameters. A candidate *accepts* the arguments when each argument by value is acceptable at the type of its parameter, the judgment Γ ⊢ e ◁ τ of {secref}[lecture-15], and each argument of a reference parameter denotes a location of the parameter's type. Collecting the candidates that accept gives the set A, and the rule chooses from A.

```
A = the candidates of cand(f, k) that accept e₁, …, eₖ
A has one element whose parameters are exactly the types of the arguments, or A is a singleton
────────────────────────────────────────────────────────────────────────────── (T-Overload)
the call of f selects that candidate
```

Three cases follow from the rule. With A empty the call fails, and the message is the one of the single candidate of that arity when there is one, so a program with a single `twice` gets the ordinary mismatch message and not a vague complaint about overloads. With A a singleton the choice is that candidate. With two or more in A the exact one wins, and if none is exact the call is *ambiguous* and the program is rejected.

An exact candidate is one whose parameter types are the types of the arguments, with no conversion at all. The conversions that may stand between an argument and a parameter are the three of the subset, `nullptr` to a pointer, a lambda to a `std::function`, and subsumption, a pointer to a derived class where a pointer to the base is expected. The last one is the one that produces ambiguity.

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

A `C*` reaches both `f(A*)` and `f(B*)` by subsumption, and neither is exact, so Core C++ rejects the call. C++ accepts it and runs `f(B*)`, because it ranks the conversion sequences and a conversion to the nearer base is better than one to the farther base.{margin}[ISO/IEC 14882:2017, clause 16.3.3, *Best viable function*.] The ranking is a page of rules, and the subset trades it for one line and a clear error. A program that needs the C++ behaviour writes the cast itself, or gives the two functions different names.

When one candidate is exact the choice is that one, and no ambiguity arises.

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

# When Two Declarations May Share a Name

%%%
tag := "distinguishable"
%%%

Not every pair of declarations may share a name. Two of them must be *distinguishable*, that is, they differ in the number of parameters, or in some position where the two types differ and neither is a `std::function`.

```
arities differ, or ∃ i. pᵢ ≠ qᵢ and neither pᵢ nor qᵢ is std::function
──────────────────────────────────────────────────────────────────── (Distinguishable)
the two declarations are overloads
```

The condition on `std::function` deserves its own reason. A lambda has no type of its own in Core C++, as {secref}[lecture-15] showed. It is checked against the `std::function` type expected at its position, which means the expected type must be known *before* the lambda is looked at. If two candidates differed only in a `std::function` parameter, choosing between them would require the type of the lambda, and giving the lambda a type would require choosing a candidate.

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

The two declarations are rejected where they stand, at the declaration, and not at some later call. That is the useful place for the message, because the author of the library learns of the problem without waiting for a client to write an ambiguous call. C++ accepts these two, because a lambda there has a closure type of its own that distinguishes the calls, at the price of the whole machinery of closure types.{fnref}[closuretype]

Two declarations with the same name and the same signature are not overloads at all, they are one declaration written twice, and the type checker reports a repeated declaration.

:::footnotes

{fnAnchor "closuretype"}[] In C++ every lambda expression has a distinct anonymous class type, and `std::function<int(int)>` is an ordinary class that stores any callable of the right shape. A call `g([=](int x) -> int { return x; })` then has an argument of closure type, and the candidates are ranked by the conversion from that type to each `std::function`. Core C++ never forms the closure type, which is the decision of Unit IV, so the information that would rank the candidates does not exist, and the subset forbids the pair instead of guessing.

:::

# Methods Overload Like Functions

%%%
tag := "method-overload"
%%%

The overload set of a method name is the set of methods with that name along the chain of the class, one per signature. A method of a derived class with the signature of a base method replaces it, which is the redefinition of {secref}[lecture-19] and requires `virtual` and `override`. A method of a derived class with the same name and a *different* signature is another overload, and requires nothing.

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

The call `deposit(v - rate)` inside the two argument method is an unqualified name, which {secref}[lecture-18] read as `this->deposit(...)`, and the overload set of `this` resolves it to the one argument method. The recursion a reader might fear does not happen, because the arities differ.

C++ has a rule Core C++ leaves out here. A member named `m` in a derived class *hides* every `m` of the base, so an overload declared in the base is unreachable through a derived object unless the derived class writes `using Base::m`. The subset takes the union along the chain instead, which loses no program and spares a rule.

# Operators Are Members

%%%
tag := "operators"
%%%

An operator in C++ is a function with a special name, and a class may give it a meaning for its own objects. In Core C++ an operator is a *member*, declared with the keyword `operator` followed by the operator itself, taking the right operand as its only parameter. The receiver is the left operand.

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

Two details of the declaration follow from decisions of earlier units. The parameter is `Point& o` and not `Ponto o`, because an object is never copied and never held by a variable, so the only way to pass one is to bind its location, which a reference parameter does. The result is `Point*` and not `Point`, for the same reason, so the operator creates the result with `new` and hands back the pointer.

The typing rule says that an infix operator whose left operand is an object is the call of the member.

```
Γ ⊢ e₁ : C    C has operator⊕ visible from Γ    Γ ⊢ e₁.operator⊕(e₂) : τ
──────────────────────────────────────────────────────────────────── (T-OpBin)
Γ ⊢ e₁ ⊕ e₂ : τ
```

The left operand decides. An operator on two `int` keeps the meaning of {secref}[lecture-8], because the left operand is an `int` and not an object, and no class may change the meaning of `1 + 2`. The operators a class may overload are the arithmetic ones, the comparisons and the indexing. The logical `&&` and `||` are excluded, because they short circuit and a member call would evaluate both operands, which would change the meaning of the operator rather than extend it.

The rewriting is not a figure of speech. The type checker replaces the infix form by the method call, and the derivation of the program shows the rule `MethodCall` where the source shows a `+`.

```lean (name := operatorTrace)
def small : String :=
  "class P {
  public:
    int x;
    P* operator+(P& o) {
      P* r = new P();
      r->x = x + o.x;
      return r;
    }
  };
  int main() {
    P* a = new P();
    a->x = 21;
    P* c = *a + *a;
    return c->x;
  }"

#eval match parseProgram small with
  | .ok p =>
    IO.println (String.intercalate "\n"
      ((renderTrace (runWith true p).2).splitOn "\n" |>.filter
        fun l => l.endsWith "(MethodCall)"))
  | .error e => IO.println e
```
```leanOutput operatorTrace
    [a ↦ ℓ2], {ℓ0 ↦ 21, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ *a + *a ⇒ ℓ4, {ℓ0 ↦ 21, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1, ℓ3 ↦ 42, ℓ4 ↦ P{x ↦ ℓ3}}   (MethodCall)
```

Once the rewriting has happened, the call is an ordinary method call. Visibility applies, so an operator declared `private` is unreachable from outside the class. Overload resolution applies, so a class may declare `operator+` twice with different parameter types. Dispatch applies, so an operator declared `virtual` in a base and redefined in a derived class is chosen by the class tag of the left operand.

# Exercises

%%%
tag := "exercises-21"
%%%

{exercise "exr-overload-print"}[] Write three declarations of `imprime`, for `int`, for `bool` and for a pointer to a class of your choice, each returning a distinct value, and a `main` that calls all three. Say for each call which candidate the rule selects and why.

{exercise "exr-overload-ambiguity"}[] Give a program with two overloads and a call that is ambiguous in Core C++ and accepted by `g++`. Compile it with `g++` and run it, and explain, from clause 16.3.3 of the standard, which candidate C++ chooses.

{exercise "exr-overload-exact"}[] Change the program of the previous exercise by one line so that the call becomes exact, and explain the change in terms of the set A of the rule.

{exercise "exr-overload-function"}[] Try to declare two functions that differ only in a `std::function` parameter, run the type checker and explain the message. Then rewrite the pair so that both remain and the call sites do not change, by adding one parameter to one of them.

{exercise "exr-operator-compare"}[] Give the class `Pair` a member `operator<` that compares by the first field, and a `main` that uses it in the condition of an `if`. Print the derivation and find the line where the comparison became a method call.

{exercise "exr-operator-short-circuit"}[] Explain, with an example that has an effect on one side, what would change in the meaning of a program if Core C++ allowed a class to overload `&&`.

```lean -show
end Lecture21
```
