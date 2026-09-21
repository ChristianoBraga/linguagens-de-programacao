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
  "class Counter {
  private:
    int value;
  public:
    Counter(int initial) { this->value = initial; }
    void increment() { value = value + 1; }
    int current() { return value; }
  };
  int main() {
    Counter* c = new Counter(40);
    c->increment();
    c->increment();
    return c->current();
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

* `this->value` is the field of the receiver by `LocArrow`.

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
  "class Box {
  private:
    int v;
  public:
    Box(int x) { v = x; }
    int twice() { return v * 2; }
  };
  int main() { Box* c = new Box(21); return c->twice(); }"

#eval match parseProgram traceCtor with
  | .ok p =>
    let ls := (renderTrace (runWith true p).2).splitOn "\n"
    IO.println (String.intercalate "\n" (ls.takeWhile (· != "𝒟₁")))
  | .error e => IO.println e
```
```leanOutput traceCtor
ρ₀ = []                       σ₀ = {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}}
ρ₁ = [this ↦ ℓ1, x ↦ ℓ2]      σ₁ = {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}
ρ₂ = [c ↦ ℓ3]                 σ₂ = {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}
ρ₃ = [this ↦ ℓ1]              σ₃ = {}
                              σ₄ = {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}}
                              σ₅ = {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}

                        𝒟₄                                                𝒟₅
  ρ₀, σ₃ ⊢ Box* c = new Box(21); ⇒ normal, ρ₂, σ₅    ρ₂, σ₅ ⊢ return c->twice(); ⇒ ret 42, ρ₂, σ₅
  ─────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₃ ⊢ main() ⇒ 42, σ₄
```

* Only the main derivation. The premises 𝒟₄ and 𝒟₅ are written apart, and the notes carry them in full.

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
