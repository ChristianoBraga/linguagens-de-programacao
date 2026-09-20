/-
Slides of Lecture 6. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Composite Types" =>

Classes with fields, objects as records of locations, `new` and field access

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-6___-Composite-Types/)

```lean -show
namespace Slides6
open CoreCpp
```

# §6.1 Classes with fields

```
class Ponto {
public:
  int x;
  int y;
};
```

* A *class* declares a composite type by its *fields*, each with a type and a name. Public fields only, methods and constructors in Unit V.

* The *class table* maps each class name to its field list. The checker reads field types there, the evaluator reads what `new` must allocate.

* A field of class type is *rejected*, it would be an object by value. A field of type `C*` is accepted.

# §6.2 Objects as records of locations

```tree
v ::= int n | bool b | void
    | loc ℓ                              a pointer, the location of an object
    | null                               the value of nullptr
    | obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]         an object, one location per field
```

* One location per field, the record at a location of its own, the *pointer* is that location.

* `p->x = 3` writes at the location of the field. Every pointer to the object sees it, *one record, no copies*.

* `Assign` already writes at a location. The only novelty is that *more expressions denote locations*.

# §6.2 No object by value

```lean (name := objectByValue)
#eval (parseProgram "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
```
```leanOutput objectByValue
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable a" (CoreCpp.Ty.cls "P")))
```

* `C*` is a type with values, the pointers. `C` is an *object type*, no variable, parameter, result or field has it.

* What the decision removes from the core. Copy constructors, assignment operators, the rules on when a copy is made.

# §6.3 Creating an object

```tree
C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
────────────────────────────────── (T-New)
Γ ⊢ new C() : C*

C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ
(ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
──────────────────────────────────────────── (New)
ρ, σ ⊢ new C() ⇒ loc ℓ, σ'
```

* One fresh location per field with the *default value*, `0`, `false`, `nullptr`, then the record. n + 1 locations, never reused.

* The defaults follow the value initialisation of C++ for `new C()`.

# §6.4 Reaching a field

```tree
ρ, σ ⊢ e ⇒ loc ℓ, σ'                 ρ, σ ⊢ e ⇒ₗ ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────── (LocDeref)    ─────────────────────────────────────────────── (LocField)
ρ, σ ⊢ *e ⇒ₗ ℓ, σ'                   ρ, σ ⊢ e.f ⇒ₗ ℓ_f, σ'

ρ, σ ⊢ e ⇒ loc ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────────────────────────────────── (LocArrow)
ρ, σ ⊢ e->f ⇒ₗ ℓ_f, σ'
```

* The location judgment now holds for `*e`, `e.f` and `e->f`, which abbreviates `(*e).f`.

# §6.4 Typing and reading

```tree
Γ ⊢ e : C*    C has τ f            Γ ⊢ e : C    C has τ f           Γ ⊢ e : τ*
──────────────────────── (T-Arrow)  ────────────────────── (T-Field)  ──────────── (T-Deref)
Γ ⊢ e->f : τ                       Γ ⊢ e.f : τ                        Γ ⊢ *e : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ'    ℓ ∈ dom σ'
──────────────────────────────── (Read)      e ∈ {*e', e'.f, e'->f, e'[i]}
ρ, σ ⊢ e ⇒ σ'(ℓ), σ'
```

* Reading a field is reading its location, *one rule* for the four forms.

# §6.4 A point

```lean (name := ponto)
def ponto : String :=
  "class Ponto {
  public:
    int x;
    int y;
  };
  int main() {
    Ponto* p = new Ponto();
    p->x = 3;
    p->y = p->x + 1;
    return p->x * 10 + p->y;
  }"

#eval (parseProgram ponto).map run
```
```leanOutput ponto
Except.ok (Except.ok (CoreCpp.Val.int 34))
```

# §6.5 The store in the derivation

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
[], {} ⊢ main() ⇒ 3, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Call)
```

# §6.6 Sharing

```lean (name := alias)
def alias : String :=
  "class Ponto { public: int x; int y; };
  int main() {
    Ponto* a = new Ponto();
    Ponto* b = a;
    b->x = 7;
    return a->x + (a == b ? 10 : 0);
  }"

#eval (parseProgram alias).map run
```
```leanOutput alias
Except.ok (Except.ok (CoreCpp.Val.int 17))
```

* Assignment copies the *pointer*, a location, not the record. Writing through one pointer is visible through the other. Equality compares locations.

# Summary

* A *class* with fields is the first composite type. The *class table* serves the checker and `new`.

* An *object* is a record of locations with a class tag, at a location of its own, reached through a *pointer*. Objects never live in variables.

* `new C()` allocates one location per field with the *default value* and then the record.

* `*e`, `e.f`, `e->f` *denote locations*, `Read` reads them, `Assign` writes them, no rule of Unit I changed.

* Two pointers to one object *share* its fields.

Exercises: see the [lecture notes](../en/Lecture-6___-Composite-Types/).

```lean -show
end Slides6
```
