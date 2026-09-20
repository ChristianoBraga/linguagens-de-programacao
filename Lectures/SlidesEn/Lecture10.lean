/-
Slides of Lecture 10. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "References and Aliasing" =>

A second name for a location, owned and aliased bindings

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-10___-References-and-Aliasing/)

```lean -show
namespace Slides10
open CoreCpp
```

# §10.1 A second name for a location

* `int& y = x` does not allocate. It binds `y` to the location of `x`.

* Two names, one location, one value. A write through either is seen through the other, *aliasing*.

```
LocalDecl ::= 'auto' VarId '=' Expr
            | Type '&'? VarId '=' Expr
```

* Still LL(1). After `Type` the next token is `&` or a variable identifier.

```lean (name := parseRef)
#eval parseStatement "int& y = x;"
```
```leanOutput parseRef
Except.ok (CoreCpp.Cmd.declRef (CoreCpp.Ty.int) "y" (CoreCpp.Expr.var "x"))
```

# §10.2 The rules

```tree
Γ ⊢ₗ e : τ    τ has values    τ well formed
───────────────────────────────────────────── (T-DeclRef)
Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ₗ ℓ, σ'
───────────────────────────────────────── (DeclRef)
ρ, σ ⊢ τ& x = e ⇒ normal, ρ[x ↦ ℓ], σ'
```

* The initialiser must *denote a location*. Where `Decl` uses ⇒, `DeclRef` uses ⇒ₗ.

* The reference has the type of its referent in Γ. Every later rule treats `y` as it treats `x`. No rule rebinds.

# §10.2 Through the reference, through the variable

```lean (name := refRun)
def alias : String :=
  "int main() {
     int x = 1;
     int& y = x;
     y = y + 41;
     return x;
   }"

#eval (parseProgram alias).map run
```
```leanOutput refRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

```lean (name := refLiteral)
#eval (parseProgram "int main() { int& r = 5; return r; }").map check
```
```leanOutput refLiteral
Except.ok (Except.error (CoreCpp.TypeError.notLvalue (CoreCpp.Expr.intLit 5)))
```

# §10.3 Owned and aliased bindings

* `Block` frees σ' ∖ (ρ' ∖ ρ). With `{ int& y = x; y = 5; }` the block adds `y ↦ ℓ0`, and ℓ0 belongs to `x` outside.

* Freeing ℓ0 would leave `x` dangling. Each binding records whether the declaration *owns* the location or *aliases* it.

* `Block` frees the owned locations of ρ' ∖ ρ only. The mark changes nothing in lookup.

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int& y = x; ⇒ normal, [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 1}   (DeclRef)
    [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 1} ⊢ y = 5; ⇒ normal, [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 5}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int& y = x; y = 5; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 5}   (Block)
```

* First construction in which *scope and lifetime* of a name come apart. The reference has its own scope and its referent's lifetime.

# §10.4 Aliasing fields and elements

```lean (name := refField)
def refField : String :=
  "class P { public: int a; int b; };
   int main() {
     P* p = new P();
     int& a = p->a;
     a = 7;
     return p->a * 10 + p->b;
   }"

#eval (parseProgram refField).map run
```
```leanOutput refField
Except.ok (Except.ok (CoreCpp.Val.int 70))
```

* Any expression that denotes a location may initialise a reference. A field, a vector element, a pointer variable.

* A pointer is a *value*, stored, reassignable, comparable with `nullptr`. A reference is a *binding*, fixed at its declaration, never null.

# §10.5 What C++ leaves undefined

* C++ binds references to temporaries, `const int& r = 5`, allows reference fields, and lets a function return a reference to a local, which *dangles*.

* Core C++ excludes the three by construction. The initialiser denotes a location, fields hold values, functions return values.

* A reference names a location of an *enclosing block*, live for the whole scope of the reference, or of an *object*, live until the program ends.

* No rule produces a reference to a freed location. `danglingLocation` is never raised by a reference.

* C++ warns about what must not happen at run time. Core C++ has two rules, and the rest does not exist.

# Summary

* A *reference* is a second name for an existing location, made by `DeclRef` with the location judgment.

* It has the type of its referent, reads by `Var`, writes by `Assign`, and is never rebound.

* Bindings are *owned* or *aliased*, and block exit frees only the owned locations.

* References reach fields, vector elements and pointer variables.

* Dangling references are impossible in Core C++, by the rules, not by a warning.

Exercises: see the [lecture notes](../en/Lecture-10___-References-and-Aliasing/).

```lean -show
end Slides10
```
