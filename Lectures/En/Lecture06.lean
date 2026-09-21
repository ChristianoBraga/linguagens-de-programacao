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

#doc (Manual) "Lecture 6: Composite Types" =>

%%%
tag := "lecture-6"
%%%

```lean -show
namespace Lecture6
open CoreCpp
```

This lecture adds the first composite type to Core C++, the class with fields. It defines objects as records of locations, gives `new` the meaning of allocating those locations, extends the location judgment to the fields, and writes the typing and evaluation rules of `new C()`, `e->f` and `e.f`. Every object is created with `new`, lives in the store, is reached through a pointer and is never copied, and the lecture explains what that decision buys.

*This lecture is also available as [presentation slides](../slides/lecture-6.en.html).*

# Classes with Fields

%%%
tag := "classes-fields"
%%%

A *class* declares a composite type by listing its *fields*, each with a type and a name. In this unit a class has public fields only, and methods, constructors and access control come in Unit V. The declaration below defines the type `Point` with two integer fields.

```
class Point {
public:
  int x;
  int y;
};
```

A class declaration is a top level declaration, next to the functions, and the *class table* of the program maps each class name to its field list. The type checker consults the table to find the type of a field, and the evaluator consults it to know which locations `new` must allocate. The declaration is well formed when every field has a type with values, so a field of class type is rejected, because it would hold an object by value. A field of pointer type to a class is accepted, and it is what {secref}[lecture-7] uses for recursive types.

# Objects as Records of Locations

%%%
tag := "objects"
%%%

An *object* of class C is a record with one location per field of C, tagged with the name of the class. The value stored at each field location is the value of the field, and the record itself is stored at a location of its own. A *pointer* to the object is that location. The value domain of Unit I gains three forms.

```
v ::= int n | bool b | void
    | loc ℓ                              a pointer, the location of an object
    | null                               the value of nullptr
    | obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]         an object, one location per field
```

The choice of locations for fields, instead of values, is what makes field update a store update. Writing `p->x = 3` writes the value 3 at the location of the field `x` of the object `p` points to, and every other pointer to the same object sees the new value, because there is one record and not two copies. The choice also keeps the rules of Unit I untouched. Assignment already writes at a location, and the only novelty is that more expressions denote locations.

The pointer type `C*` is the type of the pointers to objects of C. A variable of type `C*` holds a location, never an object. The type `C` itself is an *object type*, it has no values in the sense of {secref}[lecture-5], and the type checker rejects any variable, parameter, result or field of type `C`.

```lean (name := objectByValue)
#eval (parseProgram "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
```
```leanOutput objectByValue
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable a" (CoreCpp.Ty.cls "P")))
```

# Creating an Object

%%%
tag := "new"
%%%

The expression `new C()` creates an object of class C. Its type is `C*`, provided C is a declared class. Its evaluation allocates one fresh location per field, each holding the default value of the field type, `0` for `int`, `false` for `bool` and `nullptr` for pointers, then allocates the record at a fresh location, and evaluates to the pointer to the record. The empty parentheses are the whole argument list of this unit, because there are no constructors yet.

```
C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
────────────────────────────────── (T-New)
Γ ⊢ new C() : C*

C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ
(ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
──────────────────────────────────────────── (New)
ρ, σ ⊢ new C() ⇒ loc ℓ, σ'
```

The default values follow the value initialisation of C++ for `new C()` with empty parentheses, so a Core C++ program and its C++ compilation agree on the content of a fresh object. The rule allocates n + 1 locations, and none of them is ever reused, as the store of Unit I already promised.

# Reaching a Field

%%%
tag := "fields"
%%%

The location judgment ρ, σ ⊢ e ⇒ₗ ℓ, σ' of {secref}[lecture-3] held for variables only. It now holds for three more forms. The dereference `*e` denotes the location the pointer e holds. The field access `e.f` denotes the location of the field f in the record that e denotes. The arrow `e->f` abbreviates `(*e).f` and denotes the location of the field f in the object the pointer e points to.

```
ρ, σ ⊢ e ⇒ loc ℓ, σ'                 ρ, σ ⊢ e ⇒ₗ ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────── (LocDeref)    ─────────────────────────────────────────────── (LocField)
ρ, σ ⊢ *e ⇒ₗ ℓ, σ'                   ρ, σ ⊢ e.f ⇒ₗ ℓ_f, σ'

ρ, σ ⊢ e ⇒ loc ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────────────────────────────────── (LocArrow)
ρ, σ ⊢ e->f ⇒ₗ ℓ_f, σ'
```

The typing rules mirror the evaluation rules. The operand of `->` is a pointer to a class, the operand of `.` is a class, the operand of `*` is a pointer, and the type of the field comes from the class table.

```
Γ ⊢ e : C*    C has τ f            Γ ⊢ e : C    C has τ f           Γ ⊢ e : τ*
──────────────────────── (T-Arrow)  ────────────────────── (T-Field)  ──────────── (T-Deref)
Γ ⊢ e->f : τ                       Γ ⊢ e.f : τ                        Γ ⊢ *e : τ
```

Reading a field as a value goes through its location. One rule, `Read`, covers `*e`, `e.f`, `e->f` and the indexing of {secref}[lecture-7]. The expression denotes a location, and its value is the content of that location, which must be live.

```
ρ, σ ⊢ e ⇒ₗ ℓ, σ'    ℓ ∈ dom σ'
──────────────────────────────── (Read)      e ∈ {*e', e'.f, e'->f, e'[i]}
ρ, σ ⊢ e ⇒ σ'(ℓ), σ'
```

Assignment to a field needs no new rule. The rule `Assign` of {secref}[lecture-3] evaluates the right side, then the location of the left side by the location judgment, and writes. The program below creates a point, sets its two fields and reads them back.

```lean (name := ponto)
def ponto : String :=
  "class Point {
  public:
    int x;
    int y;
  };
  int main() {
    Point* p = new Point();
    p->x = 3;
    p->y = p->x + 1;
    return p->x * 10 + p->y;
  }"

#eval (parseProgram ponto).map run
```
```leanOutput ponto
Except.ok (Except.ok (CoreCpp.Val.int 34))
```

A field the class lacks is a static error, found by `T-Arrow` in the class table before any execution.

```lean (name := unknownField)
#eval (parseProgram "class P { public: int x; }; int main() { P* a = new P(); return a->y; }").map check
```
```leanOutput unknownField
Except.ok (Except.error (CoreCpp.TypeError.unknownField "P" "y"))
```

# A Derivation with an Object

%%%
tag := "trace-object"
%%%

The trace of a small program shows the store growing by three locations at the `new`, one for the field `x`, one for the record and one for the variable `a`, and the assignment writing through `LocArrow` at the location of the field.

```lean (name := traceObject)
#eval match parseProgram "class P { public: int x; }; int main() { P* a = new P(); a->x = 3; return a->x; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceObject
    [], {} ⊢ new P() ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}}   (New)
  [], {} ⊢ P* a = new P(); ⇒ normal, [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Decl)
    [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 3 ⇒ 3, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
        [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
      [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
    [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
  [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x = 3; ⇒ normal, [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
          [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ₗ ℓ2, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
        [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ ℓ1, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
      [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ₗ ℓ0, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
    [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ 3, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Read)
  [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ return a->x; ⇒ ret 3, [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 3, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}}   (Call)
```

The variable `a` lives at ℓ2 and holds ℓ1, the record lives at ℓ1 and holds the tag `P` with the field `x` at ℓ0, and the value 3 lands at ℓ0. The three levels, variable, record and field, are the whole model of objects of this course, and Unit V adds methods and destructors on top of it without changing it.

# Sharing

%%%
tag := "sharing"
%%%

Two pointers to the same object share its fields, because assignment copies the pointer, a location, and not the record. Writing through one pointer is visible through the other, and pointer equality compares locations.

```lean (name := alias)
def alias : String :=
  "class Point { public: int x; int y; };
  int main() {
    Point* a = new Point();
    Point* b = a;
    b->x = 7;
    return a->x + (a == b ? 10 : 0);
  }"

#eval (parseProgram alias).map run
```
```leanOutput alias
Except.ok (Except.ok (CoreCpp.Val.int 17))
```

In C++ the same program has the same result, and the decision that objects are never copied is what removes from Core C++ the copy constructors, the assignment operators and the rules about when a copy is made, a large part of the C++ standard that the course shows in real C++ without adding to the core.{margin}[ISO/IEC 14882:2017, *Programming Languages, C++*, clause 15.] Sharing is also the source of the aliasing questions that Unit III treats with references, and the model of records of locations answers them by inspection of the store.

# Exercises

%%%
tag := "exercises-6"
%%%

{exercise "exr-store-after-new"}[] Write the store after `Point* p = new Point(); Point* q = new Point(); q->x = p->x + 5;`, with the locations numbered as the interpreter numbers them, and check with the trace.

{exercise "exr-field-rules"}[] Build the derivation of `p->y = p->x + 1` in the environment and store left by `Point* p = new Point(); p->x = 3;`, naming the rules `Assign`, `LocArrow`, `Read` and `Arith` where they apply.

{exercise "exr-object-by-value"}[] Explain, by the rules `T-Decl` and `New`, why `Point q = *p;` is rejected, and say what C++ does with that declaration.

{exercise "exr-sharing"}[] Give a program with three pointers in which writing through one changes the value read through exactly one of the other two, and draw the store that explains it.

{exercise "exr-field-class"}[] The declaration `class Pair { public: Point a; Point b; };` is rejected. Rewrite it in Core C++, write the `main` that creates a pair of points, and count the locations the store holds after it.

```lean -show
end Lecture6
```
