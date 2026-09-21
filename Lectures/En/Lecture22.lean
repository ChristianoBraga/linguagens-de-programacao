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

#doc (Manual) "Lecture 22: Parametric Polymorphism" =>

%%%
tag := "lecture-22"
%%%

```lean -show
namespace Lecture22
open CoreCpp
```

Overloading gives one name to several declarations written by hand. This lecture gives one declaration to several types, which is *parametric polymorphism*. A class template is a class with a type parameter, and each instantiation is a class the compiler writes by substitution. The lecture gives the rule of instantiation, shows one template used at two types, and compares the construction with the generics of other languages, where the same idea is realised in another way.

*This lecture is also available as [presentation slides](../slides/lecture-22.en.html).*

# One Declaration, Several Types

%%%
tag := "one-declaration"
%%%

The stack of {secref}[lecture-17] holds integers. A stack of pointers to `Ponto` would be the same program with `int` replaced by `Ponto*` throughout, and writing it again is copying. The repetition is not only tedious, it is a maintenance problem, because a correction to one copy has to be made in the others.

A *class template* declares the class once with the type as a parameter.

```lean (name := stack)
def stack : String :=
  "template<typename T>
  class Pilha {
  private:
    std::vector<T>* itens;
    int topo;
  public:
    Pilha(int n) {
      this->itens = new std::vector<T>(n);
      this->topo = 0;
    }
    void empilha(T x) { (*itens)[topo] = x; topo = topo + 1; }
    T desempilha() { topo = topo - 1; return (*itens)[topo]; }
    bool vazia() { return topo == 0; }
  };
  class Ponto { public: int x; };
  int main() {
    Pilha<int>* p = new Pilha<int>(4);
    p->empilha(3);
    p->empilha(4);
    int s = p->desempilha() + p->desempilha();
    Pilha<Ponto*>* q = new Pilha<Ponto*>(2);
    Ponto* a = new Ponto();
    a->x = 35;
    q->empilha(a);
    return s + q->desempilha()->x;
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The declaration mentions `T` where the class of integers mentioned `int`, in the type of the vector, in the parameter of `empilha` and in the result of `desempilha`. The uses in `main` write `Pilha<int>` and `Pilha<Ponto*>`, and each of them is a type like any other.

The parameter is a *type* parameter, and the subset admits one of them, which the grammar enforces.

```lean (name := twoParams)
#eval parseProgram
  "template<typename T> class C { public: T v; };
  int main() { C<int, bool>* p = nullptr; return 0; }"
```
```leanOutput twoParams
Except.error "syntax error at token 23 (','): a class template of this subset has one type parameter"
```

# Instantiation Is Substitution

%%%
tag := "instantiation"
%%%

The meaning of a template is given by a rule that acts on the program, before the typing and evaluation judgments see it.

```
p has template<typename T> class C { … }    C<τ> mentioned in p    C<τ> ∉ class table of p
────────────────────────────────────────────────────────────────────────────── (Inst)
p ⟶ p, class C<τ> { … [T := τ] … }
```

Reading the rule from left to right, a program that mentions `Pilha<int>` and does not yet hold a class of that name gains one, the body of the template with `int` in place of `T`. The rule applies again while some mentioned instantiation is missing, so a template whose body mentions another template is expanded too, and the process stops when no instantiation is missing. It is idempotent, so applying it twice adds nothing, which lets the type checker and the interpreter each apply it without coordinating.

The substitution reaches every type of the body, and also the names of the classes it mentions, so a `No<T>*` inside a `Lista<T>` becomes a `No<int>*` inside `Lista<int>`. The name of an instantiation is the text the design prints for the type, so the name in the source and the name of the expanded class are the same string, and the messages of the type checker name the class the programmer wrote.

Two consequences matter for the rest of the course. The first is the *cost*. Expansion happens before the program runs, so an instantiated class is an ordinary class and a call to one of its methods is an ordinary method call. Nothing about the parameter survives into the store or the derivation, and a program that uses `Pilha<int>` runs exactly as the handwritten class of {secref}[lecture-17] does. The second is the *checking*. A template is never checked, only its instantiations are, and a template nobody instantiates is never looked at. C++ does the same in substance, with a first phase that checks what does not depend on the parameter, which the subset leaves out.

```lean (name := instantiated)
def instantiated : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
  };
  int main() { return 0; }"

#eval (parseProgram instantiated).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiated
Except.ok (Except.ok [])
```

A template alone expands to nothing, because the program mentions no instantiation. Mentioning one produces the class.

```lean (name := instantiatedTwo)
def instantiatedTwo : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
  };
  int main() {
    Caixa<int>* a = new Caixa<int>(40);
    Caixa<bool>* b = new Caixa<bool>(true);
    return a->abre() + (b->abre() ? 2 : 0);
  }"

#eval (parseProgram instantiatedTwo).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiatedTwo
Except.ok (Except.ok ["Caixa<int>", "Caixa<bool>"])
```

```lean (name := instantiatedRun)
#eval (parseProgram instantiatedTwo).map run
```
```leanOutput instantiatedRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The two instantiations are two classes, with two vectors of their own and two sets of methods. They share the source text and nothing else. In particular they are unrelated as types, which {secref}[lecture-23] takes up, and an error in the body appears once per instantiation.

An instantiation of a name that is not a template is an error of the expansion, reported before any typing.

```lean (name := notTemplate)
#eval (parseProgram
  "int main() { Pilha<int>* p = new Pilha<int>(2); return 0; }").map check
```
```leanOutput notTemplate
Except.ok (Except.error (CoreCpp.TypeError.instantiation
   "Pilha is not a class template, in the instantiation Pilha<int>"))
```

# What the Parameter May Be

%%%
tag := "parameter"
%%%

The argument of an instantiation is a type of the subset, a basic type, a pointer, a vector or a class, including another instantiation. A template may therefore be used at a type that did not exist when it was written, which is the point of the construction.

The body constrains the argument without saying so. A `Pilha<T>` stores its elements in a `std::vector<T>`, and a vector element must have a default value, so `T` must be a type with one. A template whose body compares two `T` with `<` requires a `T` that `<` accepts. Nothing in the declaration records these requirements, and the error appears at the instantiation, in the expanded class, which is the well known weakness of the construction.{margin}[B. Stroustrup, *Concepts, The Future of Generic Programming*, ISO WG21 paper N4361, 2015.]

```lean (name := badInstance)
def badInstance : String :=
  "template<typename T>
  class Par {
  public:
    T a;
    T b;
    bool ordenado() { return a < b; }
  };
  class Ponto { public: int x; };
  int main() {
    Par<Ponto*>* p = new Par<Ponto*>();
    return p->ordenado() ? 1 : 0;
  }"

#eval (parseProgram badInstance).map check
```
```leanOutput badInstance
Except.ok (Except.error (CoreCpp.TypeError.badOperand "<" (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Ponto"))))
```

The message names the operator and the type, and points inside the expanded class, not inside the template. C++ produces the same kind of message, at greater length, and the `concept` of C++20 exists to state the requirement in the declaration so that the error can be reported at the use.

# Comparison with Other Languages

%%%
tag := "comparison"
%%%

The same need, one declaration serving several types, is met in three ways in current languages, and the difference shows in what the compiler produces and in when the error appears. {numref}[tbl-generics] compares them.

:::table +header
*
  * Approach
  * Language
  * What the compiler produces
  * When the body is checked
*
  * expansion by substitution
  * C++, Core C++
  * one class per instantiation
  * at each instantiation
*
  * one implementation, erased
  * Java, from version 5
  * one class, the parameter erased to `Object`
  * once, at the declaration
*
  * one implementation, constrained
  * Haskell, Rust, Ada
  * one implementation, with a signature the parameter must satisfy
  * once, against the constraint
:::

{tabcap "tbl-generics"}[Three ways of giving one declaration to several types.]

Expansion produces fast code, because each instantiation is specialised and nothing is decided at run time, and it produces long compilations and late errors. Erasure produces one implementation and checks the body once, at the price of boxing the values and of losing the parameter at run time. A constrained implementation states in the declaration what the parameter must offer, checks the body once against that statement, and reports an error at the use when the argument does not satisfy it, which is the best of the two for the reader and asks the most of the language.

Core C++ follows C++ because the course reads C++, and the rule `Inst` is the shortest honest account of what `template` means there.

# Exercises

%%%
tag := "exercises-22"
%%%

{exercise "exr-template-queue"}[] Turn the queue of the exercises of {secref}[lecture-17] into a template, instantiate it at `int` and at a pointer to a class of your own, and run a program that uses both.

{exercise "exr-template-expansion"}[] For a template of your own, print the class table before and after the expansion with `Templates.instantiate`, and say which mention of the program produced each class.

{exercise "exr-template-nested"}[] Write a template `Lista<T>` whose body mentions `No<T>`, itself a template, and check with the class table that the expansion reaches a fixed point. Say how many classes the table holds for `Lista<int>`.

{exercise "exr-template-error"}[] Write a template whose body is correct for `int` and wrong for a pointer, instantiate it at both, and show that the message names the expanded class. Say in one sentence what a `concept` would have changed.

{exercise "exr-template-erasure"}[] Explain what the store of a program would look like if Core C++ erased the parameter as Java does, and which check the type checker would have to add at each use of `desempilha`.

{exercise "exr-template-cost"}[] Give two programs that use `Pilha<int>`, one with the template and one with the handwritten class of {secref}[lecture-17], and compare their derivations. Say what in the derivation shows that instantiation costs nothing at run time.

```lean -show
end Lecture22
```
