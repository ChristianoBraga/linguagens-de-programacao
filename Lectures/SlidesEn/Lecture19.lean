/-
Slides of Lecture 19. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Inheritance and Dispatch" =>

Subsumption, virtual methods, destructors and delete

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-19___-Inheritance-and-Dispatch/)

```lean -show
namespace Slides19
open CoreCpp
```

# §19.1 Single inheritance

```lean (name := shapes)
def shapes : String :=
  "namespace Geometria {
    class Forma {
    public:
      virtual int area() { return 0; }
      virtual ~Forma() { }
    };
    class Quadrado : public Forma {
    private:
      int lado;
    public:
      Quadrado(int l) { this->lado = l; }
      int area() override { return lado * lado; }
    };
  }
  int main() {
    Geometria::Forma* f = new Geometria::Quadrado(4);
    int a = f->area();
    delete f;
    return a;
  }"

#eval (parseProgram shapes).map run
```
```leanOutput shapes
Except.ok (Except.ok (CoreCpp.Val.int 16))
```

* Subsumption, dispatch and a virtual destructor, in one program.

# §19.2 Subsumption

```tree
D derives from B
────────────────── (Subsumption)
D* ≈ B*
```

* Applies wherever ≈ appears. Declarations, assignments, arguments, returns, comparisons, `?:`.

* The only conversion between class types. The opposite direction is a type error.

```lean (name := downcast)
def downcast : String :=
  "class Base { public: int x; };
  class Derivada : public Base { public: int y; };
  int main() { Base* b = new Derivada(); Derivada* d = b; return 0; }"

#eval (parseProgram downcast).map check
```
```leanOutput downcast
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Derivada"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Base"))))
```

# §19.2 Static type and class tag

* The type checker knows the *static type*, `Forma*`.

* The evaluator sees the *class tag* of the object in σ, `Quadrado`.

* The two may differ at every point of the program. *Dispatch* decides which one governs a method call.

# §19.3 Dispatch

```lean (name := staticDyn)
def staticDyn : String :=
  "class Base {
  public:
    int fixo() { return 1; }
    virtual int variavel() { return 10; }
  };
  class Derivada : public Base {
  public:
    int variavel() override { return 20; }
  };
  int main() { Base* b = new Derivada(); return b->fixo() + b->variavel(); }"

#eval (parseProgram staticDyn).map run
```
```leanOutput staticDyn
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

```tree
m ↦ τ m(…) { c } the method m nearest S in the chain, or nearest T when that method is virtual
```

* $`S` the static class, written into the tree by the type checker. $`T` the tag, read from the object in σ.

# §19.3 No hiding

```lean (name := hide)
def hide : String :=
  "class Base { public: int f() { return 1; } };
  class Derivada : public Base { public: int f() { return 2; } };
  int main() { return 0; }"

#eval (parseProgram hide).map check
```
```leanOutput hide
Except.ok (Except.error (CoreCpp.TypeError.redefinesNonVirtual "Derivada" "f"))
```

* A derived class redefines only a `virtual` method, and marks it `override`.

* For a non virtual method the nearest declaration from $`S` and from $`T` is the *same*. Static and dynamic dispatch agree.

* In C++ `b->f()` and `d->f()` on the same object may run different methods. Not in Core C++.

# §19.4 Destructors and delete

```tree
ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]    S the static class of e
S = T or the chain of S has a virtual destructor
the destructors of the chain of T run from T up to the root, each with this ↦ ℓ, giving σ₁
────────────────────────────────────────────────────────────────────────────────────── (Delete)
ρ, σ ⊢ delete e ⇒ normal, ρ, σ₁ ∖ {ℓ, ℓ₁, …, ℓₙ}
```

```lean (name := dtors)
def dtors : String :=
  "class Registro { public: int n; };
  class Base {
  public:
    Registro* r;
    virtual ~Base() { r->n = r->n + 1; }
  };
  class Derivada : public Base {
  public:
    ~Derivada() { r->n = r->n + 10; }
  };
  int main() {
    Registro* reg = new Registro();
    Derivada* d = new Derivada();
    d->r = reg;
    Base* b = d;
    delete b;
    return reg->n;
  }"

#eval (parseProgram dtors).map run
```
```leanOutput dtors
Except.ok (Except.ok (CoreCpp.Val.int 11))
```

# §19.4 Three undefined behaviours, three errors

```lean (name := nonVirtual)
def nonVirtual : String :=
  "class Base { public: int x; ~Base() { } };
  class Derivada : public Base { public: int y; };
  int main() { Base* b = new Derivada(); delete b; return 0; }"

#eval (parseProgram nonVirtual).map run
```
```leanOutput nonVirtual
Except.ok (Except.error (CoreCpp.Error.deleteWithoutVirtualDtor "Base" "Derivada"))
```

```lean (name := twice)
def twice : String :=
  "class Caixa { public: int v; };
  int main() { Caixa* c = new Caixa(); delete c; delete c; return 0; }"

#eval (parseProgram twice).map run
```
```leanOutput twice
Except.ok (Except.error (CoreCpp.Error.doubleDelete 1))
```

```lean (name := dangling)
def dangling : String :=
  "class Caixa { public: int v; };
  int main() { Caixa* c = new Caixa(); delete c; return c->v; }"

#eval (parseProgram dangling).map run
```
```leanOutput dangling
Except.ok (Except.error (CoreCpp.Error.danglingLocation 1))
```

# §19.4 Ownership

* The destructor does *not* free the objects the fields point to.

* A class that owns them writes `delete` on its pointers in its destructor. Ownership is taught, not checked.

* A dangling pointer is allowed to exist. Every use of it is `error`.

* `delete nullptr` does nothing. `delete` of a vector frees the elements and the record.

# Summary

* *Inheritance* extends a class. An object has the fields of the whole chain, root base first.

* *Subsumption*, $`D* ≈ B*`, is the only conversion between class types.

* *Dispatch* by the tag for `virtual` methods, by the static class otherwise, and the two agree because no method hides another.

* *delete* runs the destructors from the tag up and removes the object from σ.

* Double delete, access after delete and delete through a base without a virtual destructor are `error`.

Exercises: see the [lecture notes](../en/Lecture-19___-Inheritance-and-Dispatch/).

```lean -show
end Slides19
```
