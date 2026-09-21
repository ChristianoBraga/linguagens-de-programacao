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

#doc (Manual) "Lecture 10: References and Aliasing" =>

%%%
tag := "lecture-10"
%%%

```lean -show
namespace Lecture10
open CoreCpp
```

This lecture adds one construction to Core C++, the local reference `τ& y = e`, and uses it to study aliasing, the situation in which two names denote one location. It gives the reference its typing and evaluation rules, shows why the environment must remember which bindings allocated their location, follows a reference to a field and to a vector element, and closes with what C++ leaves undefined about references and how Core C++ excludes it by construction.

*This lecture is also available as [presentation slides](../slides/lecture-10.en.html).*

# A Second Name for a Location

%%%
tag := "second-name"
%%%

A *reference* is a name for a location that already exists. The declaration `int& y = x` does not allocate. It looks up the location of `x` and binds `y` to it, so that from that point on `x` and `y` are two names for one variable. A write through either name is seen through the other, because there is one location and one value.

The construction adds one production to the grammar of local declarations and one constructor to the abstract syntax.

```
LocalDecl ::= 'auto' VarId '=' Expr
            | Type '&'? VarId '=' Expr
```

The `&` follows the type, and the grammar stays LL(1) because after `Type` the next token is either `&` or a variable identifier. There is no `auto&` and no reference field in a class, both possible in C++, and no reference parameter yet, which Unit IV adds.

```lean (name := parseRef)
#eval parseStatement "int& y = x;"
```
```leanOutput parseRef
Except.ok (CoreCpp.Cmd.declRef (CoreCpp.Ty.int) "y" (CoreCpp.Expr.var "x"))
```

# The Rules of the Reference

%%%
tag := "rules"
%%%

The typing rule requires the initialiser to denote a location, by the judgment Γ ⊢ₗ e : τ of {secref}[lecture-6], and to have exactly the declared type. The reference enters Γ with the type of its referent, and not with a type of its own, because every later rule treats `y` as it treats `x`. Reading `y` is `Var`, writing `y` is `Assign`, and no rule rebinds a reference.

```
Γ ⊢ₗ e : τ    τ has values    τ well formed
───────────────────────────────────────────── (T-DeclRef)
Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]
```

The evaluation rule uses the location judgment in place of the evaluation judgment. Where `Decl` evaluates the initialiser to a value and allocates, `DeclRef` evaluates it to a location and binds.

```
ρ, σ ⊢ e ⇒ₗ ℓ, σ'
───────────────────────────────────────── (DeclRef)
ρ, σ ⊢ τ& x = e ⇒ normal, ρ[x ↦ ℓ], σ'
```

The program below writes through the reference and reads through the variable.

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

Two programs the type checker rejects. A literal denotes no location, so it cannot initialise a reference, and the referent must have the declared type, without the conversions the value declaration admits.

```lean (name := refLiteral)
#eval (parseProgram "int main() { int& r = 5; return r; }").map check
```
```leanOutput refLiteral
Except.ok (Except.error (CoreCpp.TypeError.notLvalue (CoreCpp.Expr.intLit 5)))
```

```lean (name := refType)
#eval (parseProgram "int main() { int x = 1; bool& b = x; return 0; }").map check
```
```leanOutput refType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "referent of b" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

# Owned and Aliased Bindings

%%%
tag := "owned"
%%%

The rule `Block` of {secref}[lecture-3] removes from σ the locations of the bindings the block added, written σ' ∖ (ρ' ∖ ρ). With references that reading is wrong. In the program below the inner block adds the binding `y ↦ ℓ0`, and ℓ0 is the location of `x`, declared outside. Removing ℓ0 at the closing brace would leave `x` dangling.

```lean (name := refScope)
def refScope : String :=
  "int main() {
     int x = 1;
     { int& y = x; y = 5; }
     return x;
   }"

#eval match parseProgram refScope with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput refScope
ρ₀ = []                    σ₀ = {}
ρ₁ = [x ↦ ℓ0]              σ₁ = {ℓ0 ↦ 1}
ρ₂ = [x ↦ ℓ0, y ↦ ℓ0]      σ₂ = {ℓ0 ↦ 5}

                   𝒟₃                                            𝒟₄                                           𝒟₅
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ { int& y = x; y = 5; } ⇒ normal, ρ₁, σ₂    ρ₁, σ₂ ⊢ return x; ⇒ ret 5, ρ₁, σ₂
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 5, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────────────── (DeclRef)
  ρ₁, σ₁ ⊢ int& y = x; ⇒ normal, ρ₂, σ₁

𝒟₂
  ────────────────── (Lit)    ──────────────────── (LocVar)
  ρ₂, σ₁ ⊢ 5 ⇒ 5, σ₁          ρ₂, σ₁ ⊢ y ⇒ₗ ℓ0, σ₁
  ───────────────────────────────────────────────────────── (Assign)
  ρ₂, σ₁ ⊢ y = 5; ⇒ normal, ρ₂, σ₂

𝒟₃
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 1 ⇒ 1, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁

𝒟₄
                   𝒟₁                                     𝒟₂
  ρ₁, σ₁ ⊢ int& y = x; ⇒ normal, ρ₂, σ₁    ρ₂, σ₁ ⊢ y = 5; ⇒ normal, ρ₂, σ₂
  ───────────────────────────────────────────────────────────────────────── (Block)
  ρ₁, σ₁ ⊢ { int& y = x; y = 5; } ⇒ normal, ρ₁, σ₂

𝒟₅
  ──────────────────── (LocVar)
  ρ₁, σ₂ ⊢ x ⇒ₗ ℓ0, σ₂
  ───────────────────────────── (Var)
  ρ₁, σ₂ ⊢ x ⇒ 5, σ₂
  ─────────────────────────────────── (Return)
  ρ₁, σ₂ ⊢ return x; ⇒ ret 5, ρ₁, σ₂
```

The block ends with the store still holding ℓ0, now with value 5. To obtain that, each binding of ρ records whether the declaration that made it *owns* the location, as `Decl` does, or *aliases* one, as `DeclRef` does. The rule `Block` reads ρ' ∖ ρ as the owned bindings the block added, and frees their locations only. The environment printed in the trace does not show the mark, because it changes nothing in lookup, only in block exit.{fnref}[alternative]

The reference has a scope of its own, the block that declares it, and shares the lifetime of its referent. This is the first construction in which scope and lifetime of a name come apart, and the separation between ρ and σ of {secref}[lecture-9] is what makes it expressible with one new rule.

:::footnotes

{fnAnchor "alternative"}[] A simpler reading, free the locations that were not in the domain of σ when the block started, fails for a reference to a field of an object created inside the block. The object may escape through a pointer stored outside, and its field location, allocated in the block, must survive. Only the ownership mark tells the location of the variable `p` from the location of the field `p->a` that the reference `r` aliases.

:::

# Aliasing Fields and Elements

%%%
tag := "fields-10"
%%%

The initialiser of a reference is any expression that denotes a location, so a reference can name a field of an object or an element of a vector. The location judgment of {secref}[lecture-6] and {secref}[lecture-7] gives the location, and the write through the reference is seen through the object.

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

A reference to a pointer variable is also a reference, of type `P*`. Assigning through it changes which object the pointer variable names, and the object created through the reference is reached through the variable.

```
class P { public: int a; };
int main() {
  P* p = nullptr;
  P*& q = p;
  q = new P();
  q->a = 3;
  return p->a;
}
```

The program returns 3, and the example `reference_pointer.cpp` of the repository compiles with `g++` to the same exit code. Pointers and references are two ways to reach a location. A pointer is a value, stored at a location of its own, that can be reassigned and compared with `nullptr`. A reference is a binding, not a value, fixed at its declaration and never null.

# What C++ Leaves Undefined

%%%
tag := "undefined"
%%%

C++ admits references that Core C++ does not. A reference may be bound to a temporary, `const int& r = 5`, and the language extends the life of the temporary to the life of the reference. A reference may be a field of a class, and a function may return a reference to a local variable, which is destroyed at the return, so the reference dangles and any use of it is undefined behaviour.

Core C++ excludes the three cases by construction. The initialiser must denote a location, so there is no temporary. A field holds a value, so there is no reference field. A function returns a value, and the reference is a local declaration whose scope ends with its block, so a reference names only a location of an enclosing block, which is live for the whole scope of the reference, or a location inside an object, which lives until the end of the program in this unit. There is no rule under which a reference names a freed location, and the property `danglingLocation`, which the interpreter reports for any access outside σ, is never raised by a reference.

The comparison sums up the method of the course. C++ describes the reference by what the programmer may write and warns about what must not happen at run time. Core C++ describes it by two rules, `T-DeclRef` and `DeclRef`, and the situations the rules do not produce do not exist.

# Exercises

%%%
tag := "exercises-10"
%%%

{exercise "exr-alias-derivation"}[] Build on paper the derivation of `int x = 1; int& y = x; int& z = y; z = 9; return x;` and say how many locations the store holds at the end.

{exercise "exr-no-rebinding"}[] In C++ as in Core C++, `y = x` with `y` a reference assigns to the referent and does not rebind `y`. Write a rule `Rebind` that would rebind a reference, say which judgment it needs in the premise, and give a program whose result changes under it.

{exercise "exr-owned-mark"}[] Give a program in which the reading of `Block` without the ownership mark, free every location of ρ' ∖ ρ, produces `danglingLocation`, and a second program in which the reading that frees the locations absent from σ at block entry produces it. Explain both with the rules.

{exercise "exr-reference-element"}[] Declare a reference to an element of a vector, write through it, and read the element. Then explain why a reference to `(*v)[i]` with `i` out of bounds is `error` at the declaration and not at the first use.

{exercise "exr-pointer-vs-reference"}[] List three differences between a pointer and a reference in Core C++ and name, for each, the rule that establishes it.

{exercise "exr-cpp-dangling"}[] Write a C++ program with a function that returns a reference to a local variable, and explain, with the rules of Core C++, which rule would have to exist for the program to be in the subset and why the course does not add it.

```lean -show
end Lecture10
```
