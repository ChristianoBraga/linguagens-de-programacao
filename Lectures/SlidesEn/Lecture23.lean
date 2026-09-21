/-
Slides of Lecture 23. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Subtyping" =>

Subsumption, the three polymorphisms, and why two of them do not compose

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-23___-Subtyping/)

```lean -show
namespace Slides23
open CoreCpp
```

# §23.1 Subsumption

```tree
Γ ⊢ e : D*    D derives from B
─────────────────────────────── (T-Sub)
Γ ⊢ e : B*
```

* From the specific to the general. Whoever has a `Square*` has a `Shape*`. The converse fails.

* Not a separate judgment. It lives in the relation τ ≈ τ', so it holds in declarations, assignments, arguments, results, comparisons and branches at once.

```lean (name := notSuper)
def notSuper : String :=
  "class Shape { public: int side; };
  class Square : public Shape { public: int mark; };
  int main() { Shape* f = new Square(); Square* q = f; return 0; }"

#eval (parseProgram notSuper).map check
```
```leanOutput notSuper
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of q"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Square"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Shape"))))
```

# §23.1 The conversion does nothing

* A pointer value is a *location*, and the location does not change when the type of the expression does.

* The object keeps its *class tag*, which is how dispatch finds the method of the derived class.

* Subsumption happens in Γ, like instantiation, and costs nothing at run time.

```lean (name := dispatch)
def dispatch : String :=
  "class Shape {
  public:
    virtual int area() { return 0; }
    virtual ~Shape() { }
  };
  class Square : public Shape {
  private:
    int side;
  public:
    Square(int l) { this->side = l; }
    int area() override { return side * side; }
  };
  int sum(Shape& f, Shape& g) { return f.area() + g.area(); }
  int main() {
    Shape* a = new Square(3);
    Shape* b = new Square(4);
    int r = sum(*a, *b);
    delete a;
    delete b;
    return r;
  }"

#eval (parseProgram dispatch).map run
```
```leanOutput dispatch
Except.ok (Except.ok (CoreCpp.Val.int 25))
```

# §23.2 Three kinds of polymorphism

:::table +header
*
  * Kind
  * What varies
  * Chosen
*
  * overloading
  * the declaration that runs
  * at compile time, by the argument types
*
  * parametric
  * the type the declaration serves
  * at compile time, by the instantiation
*
  * inclusion
  * the method that runs
  * at run time, by the class tag
:::

* Overloading, unrelated bodies under one name. Parametric, one body for a family of types. Inclusion, one interface and one body per class.

* Only *inclusion* costs anything at run time, and only it can depend on a value computed while the program runs.

# §23.3 Where the two do not compose

* Is `Stack<Square*>` a subtype of `Stack<Shape*>`. In Core C++, in C++ and in Java, *no*.

```lean (name := invariance)
def invariance : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
    void store(T x) { v = x; }
  };
  class Shape { public: int side; };
  class Square : public Shape { public: int mark; };
  int main() {
    Box<Square*>* c = new Box<Square*>(new Square());
    Box<Shape*>* d = c;
    return 0;
  }"

#eval (parseProgram invariance).map check
```
```leanOutput invariance
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Box<Shape*>"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Box<Square*>"))))
```

# §23.3 Why the refusal protects the program

* If it were allowed, `d` and `c` would name one object of class `Box<Square*>`.

* `d->store(x)` accepts any `Shape*`, so a plain `Shape` could enter a box whose `get` promises a `Square*`.

* The next `c->get()->mark` would read a field of an object that has none.

* *Covariance* in results, *contravariance* in parameters, *invariance* when the parameter is in both, as in `Box`.

* C++ and Core C++ make every instantiation invariant. Java asks at the use, Scala and Kotlin at the declaration.

# Summary

* *T-Sub*. A pointer to a derived class stands where a pointer to the base is expected, in every position of the relation τ ≈ τ'.

* The conversion is a statement about *types*, and the store is untouched, so the tag still drives the dispatch.

* Three polymorphisms, *overloading*, *parametric* and *inclusion*, and only the last decides at run time.

* Two instantiations of one template are *invariant*, and the refusal is what keeps the store consistent with the types.

Exercises: see the [lecture notes](../en/Lecture-23___-Subtyping/).

```lean -show
end Slides23
```
