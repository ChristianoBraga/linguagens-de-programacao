/-
Slides of Lecture 22. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Parametric Polymorphism" =>

One declaration, several types, expanded by substitution

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-22___-Parametric-Polymorphism/)

```lean -show
namespace Slides22
open CoreCpp
```

# §22.1 One declaration, several types

* A stack of `int` and a stack of `Point*` are the same program with one word changed. Writing both is copying.

* A *class template* declares the class once, with the type as a parameter.

* One type parameter in the subset, which the grammar enforces.

```lean (name := twoParams)
#eval parseProgram
  "template<typename T> class C { public: T v; };
  int main() { C<int, bool>* p = nullptr; return 0; }"
```
```leanOutput twoParams
Except.error "syntax error at token 23 (','): a class template of this subset has one type parameter"
```

# §22.1 A stack at two types

```lean (name := stack)
def stack : String :=
  "template<typename T>
  class Stack {
  private:
    std::vector<T>* items;
    int top;
  public:
    Stack(int n) {
      this->items = new std::vector<T>(n);
      this->top = 0;
    }
    void push(T x) { (*items)[top] = x; top = top + 1; }
    T pop() { top = top - 1; return (*items)[top]; }
    bool empty() { return top == 0; }
  };
  class Point { public: int x; };
  int main() {
    Stack<int>* p = new Stack<int>(4);
    p->push(3);
    p->push(4);
    int s = p->pop() + p->pop();
    Stack<Point*>* q = new Stack<Point*>(2);
    Point* a = new Point();
    a->x = 35;
    q->push(a);
    return s + q->pop()->x;
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

# §22.2 Instantiation is substitution

```tree
p has template<typename T> class C { … }    C<τ> mentioned in p    C<τ> ∉ class table of p
────────────────────────────────────────────────────────────────────────────── (Inst)
p ⟶ p, class C<τ> { … [T := τ] … }
```

* Applied to a *fixed point*, because the class it adds may mention another instantiation. Idempotent.

* The substitution reaches every type and every class *name*, so `Node<T>*` in `Lista<T>` becomes `Node<int>*` in `Lista<int>`.

* *Cost*. The expansion precedes the run, so an instantiated class is an ordinary class.

* *Checking*. A template is never checked, only its instantiations are.

# §22.2 Two instantiations, two classes

```lean (name := instantiatedTwo)
def instantiatedTwo : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
  };
  int main() {
    Box<int>* a = new Box<int>(40);
    Box<bool>* b = new Box<bool>(true);
    return a->get() + (b->get() ? 2 : 0);
  }"

#eval (parseProgram instantiatedTwo).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiatedTwo
Except.ok (Except.ok ["Box<int>", "Box<bool>"])
```

```lean (name := instantiatedRun)
#eval (parseProgram instantiatedTwo).map run
```
```leanOutput instantiatedRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* They share the source text and nothing else, and they have no subtype relation.

# §22.3 What the parameter may be

* Any type of the subset, including another instantiation.

* The body constrains the argument *without saying so*, and the error appears in the expanded class.

```lean (name := badInstance)
def badInstance : String :=
  "template<typename T>
  class Pair {
  public:
    T a;
    T b;
    bool sorted() { return a < b; }
  };
  class Point { public: int x; };
  int main() {
    Pair<Point*>* p = new Pair<Point*>();
    return p->sorted() ? 1 : 0;
  }"

#eval (parseProgram badInstance).map check
```
```leanOutput badInstance
Except.ok (Except.error (CoreCpp.TypeError.badOperand "<" (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Point"))))
```

* The `concept` of C++20 exists to state the requirement in the declaration, so the error lands at the use.

# §22.4 Three ways to serve several types

:::table +header
*
  * Approach
  * Language
  * The compiler produces
  * The body is checked
*
  * expansion
  * C++, Core C++
  * one class per instantiation
  * at each instantiation
*
  * erasure
  * Java
  * one class, parameter erased
  * once, at the declaration
*
  * constrained
  * Haskell, Rust, Ada
  * one implementation with a signature
  * once, against the constraint
:::

* Expansion gives fast code, long compilations and late errors. Erasure gives one implementation and boxing. A constraint gives the error at the use.

# Summary

* A *class template* gives one declaration to a family of types, with one type parameter in the subset.

* *Inst*. Instantiation is substitution, applied to a fixed point before checking and before running.

* An instantiated class is an *ordinary class*, so the construction costs nothing at run time.

* A template is *never checked*, only its instantiations are, and the error names the expanded class.

* Expansion, erasure and constrained implementation are three answers to one need.

Exercises: see the [lecture notes](../en/Lecture-22___-Parametric-Polymorphism/).

```lean -show
end Slides22
```
