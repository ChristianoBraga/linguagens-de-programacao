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

#doc (Manual) "Lecture 14: Call by Reference" =>

%%%
tag := "lecture-14"
%%%

```lean -show
namespace Lecture14
open CoreCpp
```

This lecture adds the second parameter mechanism of Core C++, call by reference. A parameter `τ& x` is bound to the location of its argument, not to a fresh copy, so a write to the parameter is a write to the argument. The lecture writes the call rule with both kinds of parameter, shows the classic swap, examines aliasing between parameters, and lists what C++ leaves undefined around references and what Core C++ excludes by construction.

*This lecture is also available as [presentation slides](../slides/lecture-14.en.html).*

# A Parameter Bound to a Location

%%%
tag := "by-reference"
%%%

{secref}[lecture-10] introduced the local reference `τ& y = e`, a second name for the location $`e` denotes. A *reference parameter* is the same construction at a call. The declaration `void inc(int& r)` says that `r` is a name for the location of whatever argument the call supplies, and the argument must therefore denote a location, a variable, a field, a dereferenced pointer or a vector element. A literal or the result of an arithmetic expression is not admitted.

In the environment of the function the binding of `r` is an alias, in the sense of {secref}[lecture-10], and the return does not free it. The call rule of {secref}[lecture-13] gains one case per parameter.

```
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
for each i, left to right, with σ'₀ = σ,
  pᵢ = τᵢ      ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)      by value, a fresh location with a copy
  pᵢ = τᵢ&     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ                               by reference, the location of the argument
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
─────────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓᵢ | pᵢ by value}
```

The two cases differ in one premise. A parameter by value evaluates its argument with ⇒, to a value, and allocates. A parameter by reference evaluates its argument with ⇒ₗ, to a location, and allocates nothing. The environment of the function binds both kinds of parameter to locations, so the body treats them alike, and only the final step distinguishes them, the copies leave the store and the referents stay.

The typing rule adds the corresponding premise. For a parameter by reference the argument is checked with the location judgment Γ ⊢ₗ, and its type must be exactly the parameter type, without the `nullptr` conversion, because `nullptr` denotes no location.

```
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
Γ ⊢ eᵢ : τᵢ' with τᵢ' ≈ τᵢ for each pᵢ = τᵢ    Γ ⊢ₗ eⱼ : τⱼ for each pⱼ = τⱼ&
──────────────────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

# Swap

%%%
tag := "swap"
%%%

The function `swap` exchanges the contents of two locations. Under call by value it would exchange two copies and leave the arguments untouched. Under call by reference the parameters are the arguments, and the exchange is visible in `main`.

```lean (name := swap)
def swap : String :=
  "void swap(int& a, int& b) { int t = a; a = b; b = t; }
   int main() { int x = 1; int y = 2; swap(x, y);
     return x * 10 + y; }"

#eval (parseProgram swap).map run
```
```leanOutput swap
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

The trace shows the mechanism. The arguments `x` and `y` are evaluated with ⇒ₗ to ℓ0 and ℓ1, and the environment of `swap` is \[a ↦ ℓ0, b ↦ ℓ1\], the same locations under new names. The local `t` receives a fresh location ℓ2. The two assignments write to ℓ0 and ℓ1, and after the call `main` reads the exchanged values through `x` and `y`. Only ℓ2 leaves the store on return, the local of the body, and the referents ℓ0 and ℓ1 stay.{fnref}[locals]

```lean (name := trocaTrace)
#eval match parseProgram swap with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput trocaTrace
    [], {} ⊢ 1 ⇒ 1, {}   (Lit)
  [], {} ⊢ int x = 1; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Decl)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ 2 ⇒ 2, {ℓ0 ↦ 1}   (Lit)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int y = 2; ⇒ normal, [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2}   (Decl)
      [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1, ℓ1 ↦ 2}   (LocVar)
      [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ y ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 2}   (LocVar)
          [a ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ a ⇒ₗ ℓ0, {ℓ0 ↦ 1, ℓ1 ↦ 2}   (LocVar)
        [a ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ a ⇒ 1, {ℓ0 ↦ 1, ℓ1 ↦ 2}   (Var)
      [a ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ int t = a; ⇒ normal, [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1}   (Decl)
          [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ b ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1}   (LocVar)
        [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ b ⇒ 2, {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1}   (Var)
        [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ a ⇒ₗ ℓ0, {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1}   (LocVar)
      [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ a = b; ⇒ normal, [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1}   (Assign)
          [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ t ⇒ₗ ℓ2, {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1}   (LocVar)
        [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ t ⇒ 1, {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1}   (Var)
        [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ b ⇒ₗ ℓ1, {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1}   (LocVar)
      [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1} ⊢ b = t; ⇒ normal, [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2], {ℓ0 ↦ 2, ℓ1 ↦ 1, ℓ2 ↦ 1}   (Assign)
    [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ swap(x, y) ⇒ void, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Call)
  [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 2} ⊢ swap(x, y); ⇒ normal, [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1}   (ExprStmt)
          [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (LocVar)
        [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ x ⇒ 2, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Var)
        [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ 10 ⇒ 10, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Lit)
      [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ x * 10 ⇒ 20, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Binary)
        [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ y ⇒ₗ ℓ1, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (LocVar)
      [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ y ⇒ 1, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Var)
    [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ x * 10 + y ⇒ 21, {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Binary)
  [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1} ⊢ return x * 10 + y; ⇒ ret 21, [x ↦ ℓ0, y ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ 1}   (Return)
[], {} ⊢ main() ⇒ 21, {}   (Call)
```

:::footnotes

{fnAnchor "locals"}[] The return of a call frees the copies of the arguments by value and the locals the body declared, read as the owned bindings the body added to the function environment. The alias bindings, the `τ&` parameters, free nothing, because they name locations that exist before the call. The rule reads ρ' ∖ ρ exactly as the block does in {secref}[lecture-10].

:::

# Any Location Is an Argument

%%%
tag := "any-location"
%%%

The argument of a reference parameter is any expression that denotes a location. A field of an object and an element of a vector qualify, and the function `inc` below increments them in place.

```lean (name := incField)
def incrementField : String :=
  "class P { public: int a; };
   void inc(int& r) { r = r + 1; }
   int main() { P* p = new P(); inc(p->a); inc(p->a);
     std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
     return p->a * 10 + (*v)[1]; }"

#eval (parseProgram incrementField).map run
```
```leanOutput incField
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

An expression without a location is rejected before execution. The literal 5 has a value and no location, and the call `inc(5)` is a type error.

```lean (name := incLit)
def incrementLiteral : String :=
  "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }"

#eval (parseProgram incrementLiteral).map check
```
```leanOutput incLit
Except.ok (Except.error (CoreCpp.TypeError.refArgument "inc" "r" (CoreCpp.Expr.intLit 5)))
```

The type of the argument must be exactly the type of the parameter. A `bool` variable is a location, but not one of type `int`.

```lean (name := incBool)
def incrementBool : String :=
  "void inc(int& r) { r = r + 1; }
   int main() { bool b = true; inc(b); return 0; }"

#eval (parseProgram incrementBool).map check
```
```leanOutput incBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument r of inc" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

# Aliasing Between Parameters

%%%
tag := "aliasing"
%%%

Two reference parameters may receive the same argument. The function `dup` below reads as if `a` and `b` were distinct, but the call `dup(x, x)` binds both to the location of `x`, and each assignment changes what the other reads. The result is 4, and not the 3 that distinct locations would give.

```lean (name := dup)
def duplicate : String :=
  "void dup(int& a, int& b) { a = a + b; b = b + a; }
   int main() { int x = 1; dup(x, x); return x; }"

#eval (parseProgram duplicate).map run
```
```leanOutput dup
Except.ok (Except.ok (CoreCpp.Val.int 4))
```

Aliasing is the price of call by reference. A function cannot assume that two reference parameters are independent, and a reader of its body cannot know, without looking at every call, whether a write to one changes the other. C++ has the same behaviour, and the rules of Core C++ make it explicit, the environment of the call maps two names to one location.

# What C++ Leaves Undefined

%%%
tag := "discrepancies"
%%%

References in C++ carry two sources of undefined behaviour that Core C++ excludes by construction. {numref}[tbl-refs] summarises.

:::table +header
*
  * Situation
  * C++17
  * Core C++
*
  * argument without a location, `inc(5)`
  * compilation error
  * type error
*
  * `const int& r = 5`, reference to a temporary
  * allowed, the temporary lives as long as `r`
  * excluded, the initialiser denotes a location
*
  * reference returned to a local that has ended
  * undefined
  * impossible, a reference is never a result
*
  * reference parameter bound to a freed object
  * undefined
  * `error`, the location is outside σ
*
  * two reference parameters to one argument
  * aliasing, defined
  * aliasing, defined
:::

{tabcap "tbl-refs"}[References at calls in C++17 and in Core C++.]

The third line is the important one. A C++ function may return a reference to one of its locals, and the caller then reads a location that no longer exists. Core C++ has no reference results, so the situation does not arise, and a reference parameter can only name a location that exists before the call, in the caller or among the objects of σ.

# Exercises

%%%
tag := "exercises-14"
%%%

{exercise "exr-swap-value"}[] Rewrite `swap` with parameters by value, run it, and explain by the two versions of the rule `Call` why the result changes.

{exercise "exr-free-locals"}[] The rule `Call` frees the copies and the locals of the body. Say which information the rule uses to tell the locals from the referents of the reference parameters, and where the interpreter keeps it.

{exercise "exr-alias-vector"}[] Write a function `void copy(int& from, int& to)` and call it with two elements of one vector, then with the same element twice. Predict both results by the rule `Call` and check with the interpreter.

{exercise "exr-ref-pointer"}[] A parameter `P*& q` is a reference to a pointer variable. Write a function that assigns `new P()` to such a parameter and show, with a trace, that the caller's pointer changes.

{exercise "exr-mechanisms"}[] Classify each parameter of the programs of this lecture by its mechanism and, for each call, list the locations that leave the store on return.

```lean -show
end Lecture14
```
