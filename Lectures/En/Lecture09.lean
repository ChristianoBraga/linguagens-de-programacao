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

#doc (Manual) "Lecture 9: Variables and Storage" =>

%%%
tag := "lecture-9"
%%%

```lean -show
namespace Lecture9
open CoreCpp
```

This lecture opens Unit III, storage and control, with the variable as its object. It returns to the environment ρ and the store σ of {secref}[lecture-3], now as the two halves of what a variable is, names the six attributes of a variable and finds each one in the rules, and reads the declaration and the assignment as the two operations that create and update storage. Shadowing and the exit of a block close the lecture, with the derivation tree the interpreter prints.

*This lecture is also available as [presentation slides](../slides/lecture-9.en.html).*

# Two Maps Instead of One

%%%
tag := "two-maps"
%%%

The simplest model of a variable is a map from names to values. In that model `x = x + 1` reads the value of `x`, adds one and rebinds `x`, and nothing else exists. Core C++ does not use that model, because it cannot express what the rest of the course needs. Two names for one variable, a name that outlives a block, an object that several pointers reach, all require a level between the name and the value.

That level is the *location*. The environment ρ maps each identifier to a location ℓ, and the store σ maps each location to a value. A variable is a pair, a binding in ρ and a location in σ. Reading `x` is reading σ(ρ(x)), and assigning to `x` is writing at ρ(x). The two maps change at different moments. A declaration extends ρ and allocates in σ. An assignment changes σ and leaves ρ alone. The exit of a block restores ρ and shrinks σ.

Watt calls the values that can be stored at a location the *storables* of the language.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, chapter 3.] In Core C++ the storables are the integers, the booleans and the pointers, exactly the types with values of {secref}[lecture-5]. An object is not a storable, it is a record of locations, and a variable of class type does not exist. That decision, taken in {secref}[lecture-6], is what keeps one object from being two after an assignment.

# The Attributes of a Variable

%%%
tag := "attributes"
%%%

A variable has six attributes, and the semantics gives each one a place. {numref}[tbl-attributes] lists them.

:::table +header
*
  * Attribute
  * Where it lives
  * Fixed by
*
  * identifier
  * the key in ρ and in Γ
  * the declaration
*
  * location
  * ρ(x)
  * the declaration, by alloc
*
  * value
  * σ(ρ(x))
  * the initialiser, then each assignment
*
  * type
  * Γ(x)
  * the declaration, checked statically
*
  * scope
  * the commands in which x is in ρ
  * the block that declares x
*
  * lifetime
  * the interval in which ρ(x) is in dom σ
  * from alloc to the exit of the block
:::

{tabcap "tbl-attributes"}[The six attributes of a variable and their place in the semantics.]

The identifier, the type and the scope are *static* attributes. The type checker knows them without running the program, and {secref}[lecture-5] showed Γ carrying the identifier and the type through the commands of a block. The location, the value and the lifetime are *dynamic*. They exist only in a derivation of the evaluation judgment, and two executions of the same declaration, in two calls of the same function, get two locations.

Scope and lifetime coincide for a local variable of Core C++, because the block that declares the variable is the block that frees its location. They come apart in the next lecture, when a reference gives a location a second name with a scope of its own, and in {secref}[lecture-6] they came apart already for objects, which live until the end of the program while the pointers that reach them come and go.

# Declaration

%%%
tag := "declaration"
%%%

The declaration `τ x = e` creates a variable. Its typing rule requires the initialiser to have the declared type, or a type compatible with it, and extends Γ. Its evaluation rule evaluates the initialiser, allocates a fresh location holding the value and extends ρ. The grammar requires the initialiser, so no variable ever holds an unknown value, a decision {secref}[lecture-2] discussed.

```
Γ ⊢ e : τ'    τ' ≈ τ    τ has values
─────────────────────────────────────── (T-Decl)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ v, σ'    (ℓ, σ″) = alloc(σ', v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

The operation alloc returns a location outside the domain of σ. Locations are never reused, so ℓ identifies this variable for the rest of the execution, even after the block frees it. The output environment ρ\[x ↦ ℓ\] is what makes the declaration reach the following commands, through the sequence rule of {secref}[lecture-3].

A declaration without initialiser is a syntax error, not a type error, because the grammar of `LocalDecl` has no alternative for it.

```lean (name := noInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput noInit
Except.error "syntax error at token 7 (';'): expected '='"
```

# Assignment

%%%
tag := "assignment"
%%%

The assignment `e₁ = e₂` updates a variable, or any other location. Its left side must denote a location, by the judgment Γ ⊢ₗ e₁ : τ, and its right side must have a compatible type. Its evaluation rule evaluates the right side first, then the location of the left side, and writes the value there. The location must be live.

```
Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ    τ has values
───────────────────────────────────────────────────── (T-Assign)
Γ ⊢ e₁ = e₂ ⊣ Γ

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

The type of a variable never changes, and the type checker rejects an assignment of a value of another type before the program runs.

```lean (name := assignBool)
#eval (parseProgram "int main() { int x = 1; x = true; return x; }").map check
```
```leanOutput assignBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "assignment to x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

Assignment is a command in Core C++, not an expression, so it has no value and `x = y = 1` is not a program. {secref}[lecture-8] gave the reasons for the separation. The consequence for this lecture is that an update of the store happens only in a command, a declaration or an assignment, or inside a function call, and never in the middle of an arithmetic expression without a call.

# Shadowing and Block Exit

%%%
tag := "shadowing"
%%%

A block may declare a variable with the name of a variable of an enclosing block. The new binding is added at the front of ρ, and the lookup finds it first, so the inner variable *shadows* the outer one for the rest of the block. The two variables have different locations, and the outer one keeps its value. When the block ends, the inner binding leaves ρ and the inner location leaves σ, and the name denotes the outer variable again.

```lean (name := shadowRun)
def shadow : String :=
  "int main() {
     int x = 1;
     { int x = 10; x = x + 1; }
     return x;
   }"

#eval (parseProgram shadow).map run
```
```leanOutput shadowRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

The derivation tree shows the two variables side by side. Inside the block ρ holds two bindings for `x`, the inner one at ℓ1, and the assignment writes at ℓ1. The rule `Block` returns the outer ρ and a store without ℓ1.

```lean (name := shadowTrace)
#eval match parseProgram shadow with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput shadowTrace
    [], {} ⊢ 1 ⇒ 1, {}   (Lit)
  [], {} ⊢ int x = 1; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Decl)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ 10 ⇒ 10, {ℓ0 ↦ 1}   (Lit)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int x = 10; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Decl)
          [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
        [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ 10, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Var)
        [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ 1 ⇒ 1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Lit)
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x + 1 ⇒ 11, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Binary)
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
    [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x = x + 1; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 11}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int x = 10; x = x + 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ 1, {ℓ0 ↦ 1}   (Var)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ return x; ⇒ ret 1, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Return)
[], {} ⊢ main() ⇒ 1, {ℓ0 ↦ 1}   (Call)
```

The printed environment lists the bindings oldest first, and the lookup reads them newest first, which is why `x ⇒ₗ ℓ1` inside the block. C++ has the same rule for shadowing, and the same rule for the end of a block, where the storage of the inner variable is released. The difference is that Core C++ makes the release visible in σ, and any later access to ℓ1 would be `error`, while C++ leaves such an access undefined. The next lecture shows how a reference can produce that access in C++ and why it cannot in Core C++.

# Exercises

%%%
tag := "exercises-9"
%%%

{exercise "exr-attributes-trace"}[] For the program of {secref}[shadowing], give the six attributes of each of the two variables named `x`, and say at which line of the derivation tree each dynamic attribute is fixed.

{exercise "exr-one-map"}[] Take the model of a variable as a map from names to values, without locations, and give a Core C++ program of Unit II whose meaning that model cannot express. Explain which attribute is missing.

{exercise "exr-alloc-never-reused"}[] Locations are never reused. Give a program in which a block declares a variable, ends, and a later block declares another, and write the store after each block. Say what would change if alloc could return a freed location.

{exercise "exr-decl-order"}[] The rule `Decl` evaluates the initialiser before allocating. Write the rule that allocates first and then evaluates, and give a program in which the two rules differ. Consider an initialiser that mentions the variable being declared.

{exercise "exr-static-dynamic-attributes"}[] For each attribute of {numref}[tbl-attributes], say whether the type checker of Core C++ needs it, and name the rule of Γ ⊢ c ⊣ Γ' that reads or writes it.

{exercise "exr-cpp-uninitialised"}[] C++ accepts `int x; return x;` and leaves the result undefined. Explain how Core C++ removes the case, and say whether it removes it statically or dynamically.

```lean -show
end Lecture9
```
