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

#doc (Manual) "Lecture 18: Objects and Classes" =>

%%%
tag := "lecture-18"
%%%

```lean -show
namespace Lecture18
open CoreCpp
```

This lecture gives objects, constructors and method calls their meaning. An object is still what it was in {secref}[lecture-6], a record of locations with a class tag, created by `new` and reached through a pointer. What changes is that `new C(args)` now runs a constructor, that `this` names the receiver inside a member body, and that a method call binds `this` and the parameters and runs the body, exactly as a function call does. The lecture writes the rules `New`, `This`, `Member` and `MethodCall` and reads the derivation tree the interpreter prints.

*This lecture is also available as [presentation slides](../slides/lecture-18.en.html).*

# Constructors

%%%
tag := "constructors"
%%%

In {secref}[lecture-6] every field of a new object received the default value of its type, zero, false or `nullptr`, and the client filled the fields afterwards. A *constructor* moves that filling into the class. It is a member named after the class, with parameters and a body, and `new C(args)` runs it right after the fields are allocated, with `this` bound to the new object.

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

The typing rule of `new` checks the arguments against the parameters of the constructor as a call does, by the rule `T-Call` of {secref}[lecture-13], and gives the expression the pointer type. A class without a constructor is created by `new C()` alone, as in Unit II.

```
C ↦ class C { … C(p₁ x₁, …, pₖ xₖ) { c } … }    arguments as in T-Call
──────────────────────────────────────────────────────────────── (T-New)
Γ ⊢ new C(e₁, …, eₖ) : C*
```

The evaluation rule allocates the fields with their defaults, then the tagged record, and then runs the constructor body as a member call, {secref}[member-call], on the fresh location.

```
C ↦ class C { … }    f₁ … fₙ the fields of the chain of C, the root base first
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ    (ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
the constructors of the chain run from the root base down, each with this ↦ ℓ, giving σ''
──────────────────────────────────────────────────────────────────────────────────────── (New)
ρ, σ ⊢ new C(e₁, …, eₖ) ⇒ loc ℓ, σ''
```

The fields of the chain and the order of the constructors matter only with inheritance, {secref}[lecture-19]. For a class without a base the chain is the class alone.

# This

%%%
tag := "this"
%%%

Inside a member body the keyword `this` denotes the object on which the member was called, the *receiver*. Its type is a pointer to the class, and it evaluates to the location of the object.

```
Γ(this) = C*                       ρ(this) = ℓ
──────────────── (T-This)          ───────────────────────── (This)
Γ ⊢ this : C*                      ρ, σ ⊢ this ⇒ loc ℓ, σ
```

The binding of `this` in ρ is made by the call, {secref}[member-call], and it is an *alias* binding in the sense of {secref}[lecture-10]. It names a location that exists before the call, the object, and the return of the member does not free it. There is no location whose content is the pointer `this`, so `this` is not a variable, cannot be assigned and denotes no location by ⇒ₗ. It is a pointer value, and `this->value` is the field `value` of the receiver by the rule `LocArrow` of {secref}[lecture-6].

A member body may also name a field or a method of the receiver without `this`. The method `increment` above writes `value` directly. The rule is a fallback on the rules for variables. A name that is not bound in the context, or in the environment, and is a member of the current class denotes the member of `this`.

```
x ∉ Γ    Γ(this) = C*    Γ ⊢ this->x : τ            x ∉ ρ    ρ(this) = ℓ    σ(ℓ) = obj C [… x ↦ ℓₓ …]
─────────────────────────────────────── (T-VarField)  ──────────────────────────────────────────────── (LocVarField)
Γ ⊢ x : τ                                             ρ, σ ⊢ x ⇒ₗ ℓₓ, σ
```

A parameter or a local variable with the name of a field hides the field, and the field is then reached only through `this`, the C++ rule as well. The constructor of `Counter` above could have been written with a parameter `value` and the body `this->value = value;`.

# Member Calls

%%%
tag := "member-call"
%%%

A method call `e->m(args)` names a receiver, a method and arguments. Its typing rule finds the method in the class of the receiver, requires it visible by the rule `Visible` of {secref}[lecture-17], and checks the arguments as a call does. The form `e.m(args)` needs a receiver of class type, an object denoted by `*p` for instance, and `e->m(args)` a receiver of pointer type.

```
Γ ⊢ e : C*    C has τ m(p₁ x₁, …, pₖ xₖ) visible from Γ    arguments as in T-Call
────────────────────────────────────────────────────────────────────────────── (T-MethodArrow)
Γ ⊢ e->m(e₁, …, eₖ) : τ
```

The evaluation follows the rule `Call` of {secref}[lecture-13] with one binding more. The receiver is evaluated to the location ℓ of the object, the arguments are bound as in a call, by value with a fresh copy and by reference with an alias, `this` is bound to ℓ as an alias, and the body runs. The return frees the copies and the locals of the body and never the receiver.

```
for each i, left to right, with σ'₀ = σ,
  pᵢ = τᵢ     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)
  pᵢ = τᵢ&    ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ
ρ_m = [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_m, σ'ₖ ⊢ c ⇒ r, ρ', σ''
─────────────────────────────────────────────────────────────── (Member)
member ℓ (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_m))

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T […]    m ↦ τ m(…) { c } the method of the class of e
member ℓ (e₁, …, eₖ) ⇒ v, σ'
───────────────────────────────────────────────────────────────────────────────────── (MethodCall)
ρ, σ ⊢ e->m(e₁, …, eₖ) ⇒ v, σ'
```

With `normal` in place of `ret v` the result is `void` for a `void` method and `error` otherwise, as for functions. The rule `Member` is shared by methods, constructors and destructors. Which method `m` of the class of `e` runs is the question of dispatch, and {secref}[lecture-19] refines the premise for virtual methods. In this lecture the class of the object and the class of the pointer coincide, and the method is the one declared in that class.

The environment of a member body holds `this` and the parameters, nothing else. A method does not see the variables of its caller, and a caller does not see the locals of the method, exactly as with functions. What the method sees beyond its parameters is the object, through `this`, and the object lives in σ, so its changes survive the return.

# The Derivation Tree of a Method Call

%%%
tag := "trace-18"
%%%

The interpreter prints the derivation of a program with a constructor and a method call. The receiver of both is the same object, at ℓ1, and its only field sits at ℓ0.

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
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceCtor
      [], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}} ⊢ 21 ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}}   (Lit)
          [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}   (Var)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
      [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v = x; ⇒ normal, [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ 21}   (Assign)
    [], {} ⊢ new Box(21) ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}}   (New)
  [], {} ⊢ Box* c = new Box(21); ⇒ normal, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Decl)
        [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ₗ ℓ3, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
      [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
            [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ 21, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ 2 ⇒ 2, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Lit)
        [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v * 2 ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Binary)
      [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return v * 2; ⇒ ret 42, [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
    [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c->twice() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (MethodCall)
  [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return c->twice(); ⇒ ret 42, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Box{v ↦ ℓ0}}   (Call)
```

The first lines are the constructor. The field `v` is allocated at ℓ0 with the default zero and the record at ℓ1 before the argument 21 is even evaluated, which is why the store of the first line already holds both. The body runs under the environment `[this ↦ ℓ1, x ↦ ℓ2]`, with the parameter at a fresh location ℓ2, and the unqualified `v` on the left of the assignment reaches ℓ0 by the rule `LocVarField`. When `New` concludes, ℓ2 has left the store and ℓ1 remains. The method call, in the lower half, binds `this` to the same ℓ1, reads `v` through it and returns 42, and the final store holds only the object, since the local `c` of `main` left with the return of the call.

# Exercises

%%%
tag := "exercises-18"
%%%

{exercise "exr-ctor-order"}[] In the derivation above the fields are allocated before the argument of `new` is evaluated. Write a program in which the argument has an effect on another object, and say whether the order is observable by a client.

{exercise "exr-this-not-lvalue"}[] Explain, by the rules `This` and `LocVar`, why `this = nullptr;` inside a method is rejected, and which rule rejects it.

{exercise "exr-hiding"}[] Write a constructor whose parameter has the name of a field, assign the field through `this` and run the program. Then remove `this->` and explain, by `T-Var` and `T-VarField`, what the assignment does instead.

{exercise "exr-method-env"}[] Write a method that mentions a local variable of its caller, run the type checker, and explain by the environment of the rule `Member` why the name is unknown.

{exercise "exr-two-objects"}[] Create two objects of `Counter` and call `increment` on each in alternation. Draw the store after each call and explain why the two receivers never interfere.

{exercise "exr-trace-read"}[] In the trace above, find the line in which ℓ2 leaves the store and the line in which ℓ3 is created, and name the rule responsible for each.

```lean -show
end Lecture18
```
