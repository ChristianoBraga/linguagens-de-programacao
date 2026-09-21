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

#doc (Manual) "Lecture 19: Inheritance and Dispatch" =>

%%%
tag := "lecture-19"
%%%

```lean -show
namespace Lecture19
open CoreCpp
```

This lecture treats the two constructions that make a class more than an abstract data type. *Inheritance* lets a class extend another with fields and methods, and *dynamic dispatch* lets a call through a pointer to the base run the method of the derived class of the object. The lecture writes subsumption as a typing rule, dispatch as a premise of the rule `MethodCall`, and the destructor and `delete` as the end of an object's life, with the three cases C++17 leaves undefined turned into `error`.

*This lecture is also available as [presentation slides](../slides/lecture-19.en.html).*

# Single Inheritance

%%%
tag := "inheritance"
%%%

A class `D : public B` *derives* from `B`. An object of `D` has every field of `B` and then the fields of `D`, and a method of `B` applies to it unless `D` redefines the method. The classes `B`, `D` and every class deriving from `D` form a *chain*, and the class table of {secref}[lecture-17] answers every question about a class by walking its chain up to the root.

```lean (name := shapes)
def shapes : String :=
  "namespace Geometry {
    class Shape {
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
  }
  int main() {
    Geometry::Shape* f = new Geometry::Square(4);
    int a = f->area();
    delete f;
    return a;
  }"

#eval (parseProgram shapes).map run
```
```leanOutput shapes
Except.ok (Except.ok (CoreCpp.Val.int 16))
```

The program shows the three constructions of the lecture at once. A `Square*` is stored in a variable of type `Shape*`, *subsumption*. The call `f->area()` runs the method of `Square` although the pointer has type `Shape*`, *dispatch*. The `delete f` through the base pointer reaches the object because the destructor of `Shape` is `virtual`. The classes sit in a namespace, {secref}[lecture-20].

# Subsumption

%%%
tag := "subsumption"
%%%

A pointer to a derived class is accepted wherever a pointer to its base is expected. The relation τ ≈ τ' of {secref}[lecture-8], which said when the type of a value is accepted at an expected type, gains one case.

```
D derives from B
────────────────── (Subsumption)
D* ≈ B*
```

The rule applies in declarations, assignments, arguments, returns, comparisons and the branches of `?:`, wherever ≈ appears in a premise. It is the only conversion between class types. The opposite direction, a `B*` where a `D*` is expected, is a type error, because the object behind a `B*` may be a plain `B` without the fields of `D`.

```lean (name := downcast)
def downcast : String :=
  "class Base { public: int x; };
  class Derived : public Base { public: int y; };
  int main() { Base* b = new Derived(); Derived* d = b; return 0; }"

#eval (parseProgram downcast).map check
```
```leanOutput downcast
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Derived"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Base"))))
```

Subsumption gives the language *subtyping*, the concept of Unit VI, in its simplest form. The type of an expression, `Shape*`, may be a proper supertype of the type of the object it denotes, `Square*`, and the two can differ at every point of the program. The type checker knows only the first, the *static type*. The evaluator sees only the second, the *class tag* of the object in σ. Dispatch is the rule that decides which one governs a method call.

# Dispatch

%%%
tag := "dispatch"
%%%

A method marked `virtual` is chosen by the class tag of the receiver, the nearest declaration in the chain of the tag, so a call through a base pointer reaches the redefinition of the derived class. A method that is not `virtual` is chosen by the static class of the receiver.

```lean (name := staticDyn)
def staticDyn : String :=
  "class Base {
  public:
    int fixed() { return 1; }
    virtual int dispatched() { return 10; }
  };
  class Derived : public Base {
  public:
    int dispatched() override { return 20; }
  };
  int main() { Base* b = new Derived(); return b->fixed() + b->dispatched(); }"

#eval (parseProgram staticDyn).map run
```
```leanOutput staticDyn
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

The premise of `MethodCall` that {secref}[lecture-18] left open reads as follows, with $`S` the static class of the receiver and $`T` the class tag of the object.

```
m ↦ τ m(…) { c } the method m nearest S in the chain, or nearest T when that method is virtual
```

The static class comes from the type checker. Neither ρ nor σ carries types, so after a program is checked the type checker writes into every method call the class the receiver has in Γ, and the evaluator reads it there. The tag comes from the object in σ.

Core C++ adds a restriction C++ lacks. A derived class redefines a method only when the base declares it `virtual`, and then marks it `override`. Redefining a non virtual method, which in C++ *hides* the method of the base, is a type error.

```lean (name := hide)
def hide : String :=
  "class Base { public: int f() { return 1; } };
  class Derived : public Base { public: int f() { return 2; } };
  int main() { return 0; }"

#eval (parseProgram hide).map check
```
```leanOutput hide
Except.ok (Except.error (CoreCpp.TypeError.redefinesNonVirtual "Derived" "f"))
```

The restriction has a pleasant consequence. For a non virtual method, the nearest declaration from $`S` and the nearest from $`T` are the same, because no class between $`T` and $`S` redeclares it. Static and dynamic dispatch then agree on every method that is not `virtual`, and a program that hides a method, the classical source of surprise in C++, cannot be written.{fnref}[hiding]

:::footnotes

{fnAnchor "hiding"}[] In C++ the call `b->f()` above runs `Base::f`, because `f` is not virtual and `b` has static type `Base*`, while `d->f()` on a `Derived*` to the same object runs `Derived::f`. The same object answers the same message in two ways depending on the type of the pointer that names it, and the compiler emits no diagnostic. The `override` keyword of C++11 catches only the opposite mistake, a method meant to override that does not. Core C++ requires `override` on every redefinition and forbids the hiding case, so the two dispatch policies can only differ on virtual methods, where the difference is the point.

:::

# Destructors and delete

%%%
tag := "delete"
%%%

An object created by `new` lives in σ until `delete` or the end of the program. The command `delete e` evaluates `e` to the location of an object, runs the *destructors* of its chain from the tag up to the root, each with `this` bound to the object, and removes the record and the field locations from σ.

```
Γ ⊢ e : C*                    Γ ⊢ e : std::vector<τ>*
──────────────── (T-Delete)   ──────────────────────── (T-DeleteVec)
Γ ⊢ delete e ⊣ Γ              Γ ⊢ delete e ⊣ Γ

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]    S the static class of e
S = T or the chain of S has a virtual destructor
the destructors of the chain of T run from T up to the root, each with this ↦ ℓ, giving σ₁
────────────────────────────────────────────────────────────────────────────────────── (Delete)
ρ, σ ⊢ delete e ⇒ normal, ρ, σ₁ ∖ {ℓ, ℓ₁, …, ℓₙ}
```

A destructor is a member `~C()` without parameters and without result, and a class has at most one. The order, derived first and base last, is the reverse of the constructors. A program can observe it through an object that both destructors update.

```lean (name := dtors)
def dtors : String :=
  "class Record { public: int n; };
  class Base {
  public:
    Record* r;
    virtual ~Base() { r->n = r->n + 1; }
  };
  class Derived : public Base {
  public:
    ~Derived() { r->n = r->n + 10; }
  };
  int main() {
    Record* rec = new Record();
    Derived* d = new Derived();
    d->r = rec;
    Base* b = d;
    delete b;
    return rec->n;
  }"

#eval (parseProgram dtors).map run
```
```leanOutput dtors
Except.ok (Except.ok (CoreCpp.Val.int 11))
```

The destructor of `Base` is `virtual`, and that is what makes `delete b` through the base pointer well defined. The premise `S = T or the chain of S has a virtual destructor` states the C++17 condition. When the static class differs from the tag and no class in the chain of the static class declares a virtual destructor, C++ leaves the behaviour undefined, typically running only the destructor of the base, and Core C++ makes it `error`.

```lean (name := nonVirtual)
def nonVirtual : String :=
  "class Base { public: int x; ~Base() { } };
  class Derived : public Base { public: int y; };
  int main() { Base* b = new Derived(); delete b; return 0; }"

#eval (parseProgram nonVirtual).map run
```
```leanOutput nonVirtual
Except.ok (Except.error (CoreCpp.Error.deleteWithoutVirtualDtor "Base" "Derived"))
```

Two more cases are undefined in C++ and `error` in Core C++, both by the rule that a location outside σ is `error`. A second `delete` of the same object finds no object at the location.

```lean (name := twice)
def twice : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; delete c; return 0; }"

#eval (parseProgram twice).map run
```
```leanOutput twice
Except.ok (Except.error (CoreCpp.Error.doubleDelete 1))
```

An access after `delete` finds no location for the field.

```lean (name := dangling)
def dangling : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; return c->v; }"

#eval (parseProgram dangling).map run
```
```leanOutput dangling
Except.ok (Except.error (CoreCpp.Error.danglingLocation 1))
```

The pointer `c` still holds ℓ1 after the `delete`, a *dangling pointer*. Core C++ does not forbid it, since forbidding it would need an analysis of every path of the program, but every use of it is `error` rather than a silent read of freed memory. The destructor does not free the objects the fields point to. A class that owns them writes `delete` on its pointers in its destructor, and ownership is taught, not checked, as the design states. `delete nullptr` does nothing, and `delete` of a vector frees its elements and the record, both as in C++.

# The Derivation Tree of a delete

%%%
tag := "trace-19"
%%%

```lean (name := traceDelete)
def traceDelete : String :=
  "class Box {
  public:
    int v;
    ~Box() { v = 0; }
  };
  int main() { Box* c = new Box(); c->v = 7; delete c; return 1; }"

#eval match parseProgram traceDelete with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceDelete
    [], {} ⊢ new Box() ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}}   (New)
  [], {} ⊢ Box* c = new Box(); ⇒ normal, [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Decl)
    [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 7 ⇒ 7, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
        [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
      [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
    [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c->v ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
  [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c->v = 7; ⇒ normal, [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
      [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ₗ ℓ2, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
    [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
      [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 0 ⇒ 0, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
      [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
    [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ v = 0; ⇒ normal, [this ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
  [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ delete c; ⇒ normal, [c ↦ ℓ2], {ℓ2 ↦ ℓ1}   (Delete)
    [c ↦ ℓ2], {ℓ2 ↦ ℓ1} ⊢ 1 ⇒ 1, {ℓ2 ↦ ℓ1}   (Lit)
  [c ↦ ℓ2], {ℓ2 ↦ ℓ1} ⊢ return 1; ⇒ ret 1, [c ↦ ℓ2], {ℓ2 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 1, {}   (Call)
```

The `delete` line evaluates `c`, runs the destructor body under `[this ↦ ℓ1]`, which writes zero into the field, and concludes with a store in which ℓ0 and ℓ1 are gone. Only ℓ2, the variable `c` of `main`, remains, and its content is still ℓ1, the dangling pointer. The `return` of `main` then frees ℓ2 and the final store is empty. Every object created by the program has been deleted.

# Exercises

%%%
tag := "exercises-19"
%%%

{exercise "exr-chain-fields"}[] Write three classes in a chain, each with one field, create an object of the most derived one and write the record the rule `New` builds, with the order of the fields.

{exercise "exr-dispatch-both"}[] Add a non virtual method to `Derived` in {secref}[dispatch] that does not exist in `Base`, and call it through a `Derived*` and through a `Base*`. Explain both outcomes by the rules.

{exercise "exr-hiding-cpp"}[] Compile the program of `hide` with `g++`, call `f` through a `Base*` and through a `Derived*` to the same object, and report the two results. Explain why Core C++ rejects the program instead.

{exercise "exr-dtor-order"}[] Extend the chain of {secref}[delete] with a third class whose destructor adds 100 to the record, and predict the result before running.

{exercise "exr-ownership"}[] Write a class that owns a vector through a pointer field and frees it in its destructor. Then remove the `delete` from the destructor and explain what remains in σ at the end of the program, and why Core C++ does not report it.

{exercise "exr-undefined-three"}[] For each of the three undefined cases of C++17 in this lecture, write a Core C++ program that produces the corresponding `error`, and compile it with `g++` to observe what the compiled program does.

```lean -show
end Lecture19
```
