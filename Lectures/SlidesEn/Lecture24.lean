/-
Slides of Lecture 24. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Type Inference" =>

How much of the typing a language takes over, from `auto` to Hindley and Milner

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-24___-Type-Inference/)

```lean -show
namespace Slides24
open CoreCpp
```

# §24.1 What `auto` does

```tree
Γ ⊢ e : τ    τ has values    τ ≠ nullptr_t
─────────────────────────────────────────── (T-Auto)
Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]
```

* The rule of Unit III, with no new case in Unit VI. A pointer has values and an instantiation is a class.

* The gain is in the *writing*, not in the checking. The variable has a type as definite as a written one.

```lean (name := autoInst)
def autoInst : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
  };
  int main() {
    auto c = new Box<int>(42);
    auto n = c->get();
    delete c;
    return n;
  }"

#eval (parseProgram autoInst).map run
```
```leanOutput autoInst
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

# §24.2 Local inference and its limit

* The inference is *local*. One declaration, the type of an expression it can already type, and no further.

* It never runs backwards, from a use to a declaration, and never solves for an unknown.

* A parameter and a result are always written.

```lean (name := autoParam)
#eval parseProgram
  "auto f(auto x) { return x; }
  int main() { return f(1); }"
```
```leanOutput autoParam
Except.error "syntax error at token 0 ('auto'): expected basic type"
```

* C++20 admits the parameter, as an abbreviated function template, and C++14 the result, from the `return`. The subset admits neither.

# §24.3 Inference over a whole program

```
comprimento [] = 0
comprimento (x : xs) = 1 + comprimento xs
```

* Hindley and Milner. A type variable per unknown, *constraints* collected from the body, solved by unification.

* The answer is `comprimento :: [a] -> Int`, the *most general* type, with no annotation at all.

* One implementation for every `a`, checked *once*, against a template expanded and checked once per instantiation.

* Subtyping, overloading and a parameter used at two types in one body each break the single most general solution.

# §24.3 How much each language takes over

:::table +header
*
  * Language
  * Inferred
  * Written
*
  * C, Pascal
  * nothing
  * every type
*
  * Core C++, C++, Java, Rust
  * the type of a local declaration
  * parameters and results
*
  * Haskell, OCaml
  * every type
  * nothing, and an annotation is a check
:::

* Haskell recovers overloading by the *type class*, which keeps the constraint in the type instead of resolving it at the call.

# §24.4 The unit in one program

```lean (name := whole)
def whole : String :=
  "template<typename T>
  class Vect {
  private:
    std::vector<T>* data;
  public:
    Vect(int n) { this->data = new std::vector<T>(n); }
    T& operator[](int i) { return (*data)[i]; }
    ~Vect() { delete data; }
  };
  class Point {
  public:
    int x;
    Point* operator+(Point& o) {
      Point* r = new Point();
      r->x = x + o.x;
      return r;
    }
  };
  int sum(int a) { return a; }
  int sum(int a, int b) { return a + b; }
  int main() {
    auto v = new Vect<int>(2);
    (*v)[0] = 20;
    (*v)[1] = sum(20, 2);
    int s = sum((*v)[0]) + (*v)[1];
    Point* p = new Point();
    p->x = 0;
    Point* q = *p + *p;
    int r = s + q->x;
    delete v;
    delete p;
    delete q;
    return r;
  }"

#eval (parseProgram whole).map check
```
```leanOutput whole
Except.ok (Except.ok ())
```

```lean (name := wholeRun)
#eval (parseProgram whole).map run
```
```leanOutput wholeRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* A template with a member that returns a reference, an operator member, two overloads and an `auto`.

# Summary

* `auto` copies the type of the *initialiser*, and reaches pointers and instantiations with no new rule.

* The inference is *local*, and parameters and results are always written.

* *Hindley and Milner* infers a whole program, and subtyping and overloading are what stand in its way.

* The unit in one program. Instantiation leaves no trace, an overloaded call is an ordinary call, and an operator and an indexing are *method calls*.

* `v[i]` is a method call that returns `int&`, which the design stated and the unit made true.

Exercises: see the [lecture notes](../en/Lecture-24___-Type-Inference/).

```lean -show
end Slides24
```
