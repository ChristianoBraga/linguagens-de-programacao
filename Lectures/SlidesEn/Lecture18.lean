/-
Slides of Lecture 18. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Objects and Classes" =>

Constructors, this, method calls and the derivation tree of a call

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-18___-Objects-and-Classes/)

```lean -show
namespace Slides18
open CoreCpp
```

# §18.1 Constructors

```lean (name := counter)
def counter : String :=
  "class Contador {
  private:
    int valor;
  public:
    Contador(int inicial) { this->valor = inicial; }
    void incrementa() { valor = valor + 1; }
    int atual() { return valor; }
  };
  int main() {
    Contador* c = new Contador(40);
    c->incrementa();
    c->incrementa();
    return c->atual();
  }"

#eval (parseProgram counter).map run
```
```leanOutput counter
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* A member named after the class. `new C(args)` runs it after the fields are allocated, with `this` bound to the object.

# §18.1 The rules of new

```tree
C ↦ class C { … C(p₁ x₁, …, pₖ xₖ) { c } … }    arguments as in T-Call
──────────────────────────────────────────────────────────────── (T-New)
Γ ⊢ new C(e₁, …, eₖ) : C*

f₁ … fₙ the fields of the chain of C, the root base first
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ)    (ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
the constructors of the chain run from the root down, each with this ↦ ℓ, giving σ''
────────────────────────────────────────────────────────────────────────────────── (New)
ρ, σ ⊢ new C(e₁, …, eₖ) ⇒ loc ℓ, σ''
```

* Fields with their defaults, then the tagged record, then the constructor bodies.

# §18.2 This

```tree
Γ(this) = C*                       ρ(this) = ℓ
──────────────── (T-This)          ───────────────────────── (This)
Γ ⊢ this : C*                      ρ, σ ⊢ this ⇒ loc ℓ, σ
```

* `this` is the *receiver*. An alias binding made by the call, never freed by the return.

* Not a variable. No location holds it, it cannot be assigned, it denotes no location by ⇒ₗ.

* `this->valor` is the field of the receiver by `LocArrow`.

# §18.2 Unqualified members

```tree
x ∉ Γ    Γ(this) = C*    Γ ⊢ this->x : τ
─────────────────────────────────────── (T-VarField)
Γ ⊢ x : τ

x ∉ ρ    ρ(this) = ℓ    σ(ℓ) = obj C [… x ↦ ℓₓ …]
──────────────────────────────────────────────── (LocVarField)
ρ, σ ⊢ x ⇒ₗ ℓₓ, σ
```

* A name that is not a variable and is a member of the current class denotes the member of `this`.

* A parameter or local with the name of a field *hides* the field, reached then only through `this`.

# §18.3 Member calls

```tree
Γ ⊢ e : C*    C has τ m(p₁ x₁, …, pₖ xₖ) visible from Γ    arguments as in T-Call
────────────────────────────────────────────────────────────────────────────── (T-MethodArrow)
Γ ⊢ e->m(e₁, …, eₖ) : τ

ρ_m = [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_m, σ'ₖ ⊢ c ⇒ r, ρ', σ''
─────────────────────────────────────────────────────────────── (Member)
member ℓ (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_m))

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T […]    m the method of the class of e
member ℓ (e₁, …, eₖ) ⇒ v, σ'
─────────────────────────────────────────────────────────────── (MethodCall)
ρ, σ ⊢ e->m(e₁, …, eₖ) ⇒ v, σ'
```

* The rule `Call` with one binding more. `Member` is shared by methods, constructors and destructors.

# §18.3 What a method sees

* The environment of a member body holds `this` and the parameters, *nothing else*.

* A method does not see the caller's variables. The caller does not see the method's locals.

* What the method sees beyond the parameters is the *object*, through `this`, and the object lives in σ, so its changes survive the return.

* Which `m` runs is *dispatch*, Lecture 19. Here the class of the object and of the pointer coincide.

# §18.4 The derivation tree of a call

```lean (name := traceCtor)
def traceCtor : String :=
  "class Caixa {
  private:
    int v;
  public:
    Caixa(int x) { v = x; }
    int dobro() { return v * 2; }
  };
  int main() { Caixa* c = new Caixa(21); return c->dobro(); }"

#eval match parseProgram traceCtor with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceCtor
      [], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}} ⊢ 21 ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (Lit)
          [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (Var)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
      [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v = x; ⇒ normal, [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (Assign)
    [], {} ⊢ new Caixa(21) ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (New)
  [], {} ⊢ Caixa* c = new Caixa(21); ⇒ normal, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Decl)
        [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ₗ ℓ3, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
      [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
            [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ 21, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ 2 ⇒ 2, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Lit)
        [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v * 2 ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Binary)
      [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return v * 2; ⇒ ret 42, [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
    [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c->dobro() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (MethodCall)
  [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return c->dobro(); ⇒ ret 42, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (Call)
```

# §18.4 Reading the tree

* The field ℓ0 and the record ℓ1 exist before the argument 21 is evaluated.

* The constructor runs under `[this ↦ ℓ1, x ↦ ℓ2]`. The unqualified `v` reaches ℓ0 by `LocVarField`. ℓ2 leaves at the end of `New`.

* The method call binds `this` to the *same* ℓ1 and returns 42.

* The final store holds only the object. The local `c` left with the return of `main`.

# Summary

* A *constructor* is run by `new C(args)` after the fields are allocated, with `this` bound to the object.

* `this` is the receiver, an *alias* binding, a pointer value and not a variable.

* An unqualified member name inside a body denotes the member of `this`.

* A *method call* is the rule `Call` plus the binding of `this`. The body sees `this`, the parameters and the object in σ.

* The derivation tree shows every location entering and leaving the store.

Exercises: see the [lecture notes](../en/Lecture-18___-Objects-and-Classes/).

```lean -show
end Slides18
```
