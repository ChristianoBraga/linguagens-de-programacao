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

#doc (Manual) "Lecture 11: Commands and Control" =>

%%%
tag := "lecture-11"
%%%

```lean -show
namespace Lecture11
open CoreCpp
```

This lecture treats the commands of Core C++ as a whole. It separates the three forms of control, sequence, selection and repetition, gives each its rules, explains the control result that lets `return` interrupt a sequence and a loop, and reads the block as the construction that fixes scope and lifetime. The rules were written in {secref}[lecture-3], and the lecture returns to them with the vocabulary of Unit III and with programs the interpreter runs.

*This lecture is also available as [presentation slides](../slides/lecture-11.en.html).*

# Sequence

%%%
tag := "sequence"
%%%

The simplest control is the *sequence*, one command after another. Its rule carries the environment and the store from each command to the next, so a declaration reaches the commands that follow it and an assignment is seen by them. The rule has two cases, because a command may end in `normal` or in `ret v`, and in the second case the rest of the sequence is not executed.

```
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁
```

The *control result* r is what a command hands to its context. `normal` says that execution continues, `ret v` says that a `return` was executed with value v and that everything up to the enclosing call must stop. The result is not a value of the language, and no expression can observe it. It exists in the semantics to give `return` a meaning without a jump.

# Block

%%%
tag := "block"
%%%

A *block* is a sequence between braces. Its rule runs the sequence and then undoes what the sequence did to the environment, keeps what it did to the store, and frees the locations the sequence allocated.

```
ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ', σ'
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ' ∖ (ρ' ∖ ρ)
```

The three parts of the conclusion correspond to three facts about blocks. The control r passes through, so a `return` inside a block returns from the function. The environment ρ is restored, so the names declared in the block are not visible after it, which is *scope*. The store loses the owned locations of ρ' ∖ ρ, so the variables declared in the block cease to exist, which is *lifetime*. {secref}[lecture-10] explained why only the owned bindings are freed, so that a reference never removes the location it names.

Every branch of `if`, every body of `while` and `for`, and every function body is a block, by the grammar. Core C++ has no single command as a branch, so scope is always delimited by braces and the reading of a program never depends on where a semicolon falls.

# Selection

%%%
tag := "selection"
%%%

The conditional command `if (e) {c₁} else {c₂}` evaluates the condition and executes one of the two blocks. One rule per value of the condition, and the store the condition produced is the one the branch starts from, because the condition may call a function with effects.

```
ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c₁} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-T)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂

ρ, σ ⊢ e ⇒ bool false, σ₁    ρ, σ₁ ⊢ {c₂} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-F)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂
```

An `if` without `else` is an `if` with an empty second block, and the parser produces exactly that, as {secref}[lecture-2] showed. The condition has type `bool`, and an `int` condition, which C++ converts, is a type error in Core C++.

The derivation of a selection shows the block of the chosen branch and nothing of the other. In the trace below the interpreter names both rules `If`.

```lean (name := ifTrace)
def halve : String :=
  "int main() {
     int x = 2;
     if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
     return x;
   }"

#eval match parseProgram halve with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput ifTrace
    [], {} ⊢ 2 ⇒ 2, {}   (Lit)
  [], {} ⊢ int x = 2; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 2}   (Decl)
          [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 2}   (LocVar)
        [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x ⇒ 2, {ℓ0 ↦ 2}   (Var)
        [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ 2 ⇒ 2, {ℓ0 ↦ 2}   (Lit)
      [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x % 2 ⇒ 0, {ℓ0 ↦ 2}   (Binary)
      [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ 0 ⇒ 0, {ℓ0 ↦ 2}   (Lit)
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x % 2 == 0 ⇒ true, {ℓ0 ↦ 2}   (Binary)
            [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 2}   (LocVar)
          [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x ⇒ 2, {ℓ0 ↦ 2}   (Var)
          [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ 2 ⇒ 2, {ℓ0 ↦ 2}   (Lit)
        [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x / 2 ⇒ 1, {ℓ0 ↦ 2}   (Binary)
        [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 2}   (LocVar)
      [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x = x / 2; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Assign)
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ { x = x / 2; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
  [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ if (x % 2 == 0) { x = x / 2; } else { x = x - 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (If)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ 1, {ℓ0 ↦ 1}   (Var)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ return x; ⇒ ret 1, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Return)
[], {} ⊢ main() ⇒ 1, {ℓ0 ↦ 1}   (Call)
```

# Repetition

%%%
tag := "repetition"
%%%

The loop `while (e) {c}` has three rules. When the condition is false the loop ends in `normal`. When it is true and the body ends in `normal`, the whole loop is executed again in the store the body left, and the rule recurs on its own conclusion. When the body ends in `ret v`, the loop stops and hands `ret v` up.

```
ρ, σ ⊢ e ⇒ bool false, σ₁
──────────────────────────────────────── (While-F)
ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂    ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
────────────────────────────────────────────────────────────────────────────────────── (While-T)
ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
────────────────────────────────────────────────────── (While-Ret)
ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂
```

A derivation of a loop that runs n times nests n applications of `While-T` and one of `While-F`, one inside the other, and its height grows with n. The derivation of a loop that never ends does not exist, as {secref}[lecture-3] noted, and the interpreter does not terminate on it. The program below shows the third rule at work, a `return` inside the body of a loop whose condition never becomes false.

```lean (name := whileRet)
def untilSeven : String :=
  "int main() {
     int i = 0;
     while (true) {
       i = i + 1;
       if (i == 7) { return i; }
     }
   }"

#eval (parseProgram untilSeven).map run
```
```leanOutput whileRet
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

The `return` inside the `if` inside the `while` produces `ret 7`. The rule `If-T` passes it through, `Seq-Ret` stops the body, `While-Ret` stops the loop, and `Call` consumes it. Four rules, and no jump.

The loop `for (c₀; e; cₛ) {c}` is defined through `while`. The initialiser runs once and its variable has the whole loop as scope, the body is a block of its own, and the step runs after the body, outside the scope of the body.

```
ρ, σ ⊢ c₀ ⇒ normal, ρ₀, σ₀    ρ₀, σ₀ ⊢ while (e) { {c} cₛ } ⇒ r, ρ₀, σ₁
────────────────────────────────────────────────────────────────────── (For)
ρ, σ ⊢ for (c₀; e; cₛ) {c} ⇒ r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)
```

The conclusion frees the location of the loop variable, with the same reading of ownership as `Block`. A `for` whose body declares a variable with the name of the loop variable shadows it inside the body and not in the step, because the body is its own block.

# Control Without Jumps

%%%
tag := "no-jumps"
%%%

Core C++ has no `break`, no `continue`, no `goto` and no exceptions. The only way out of a loop is its condition or a `return`, and the only way out of a function is its `return` or the end of a `void` body. The choice is deliberate. Each of the missing constructions is a non local transfer of control, and each would need either a new control result, like `brk` next to `ret`, or a semantics with continuations. The course adds one control result, `ret`, and shows with it how the others would enter.

The exercise of writing the rules of `break` is the standard way to see what the control result buys. A `brk` result would be produced by the command, passed through by `If` and `Seq-Ret`, consumed by `While` as `normal`, and rejected by the type checker outside a loop. The last point is what C++ does, and it is the first place in the course where the type checker must know in which construction a command occurs.

# Exercises

%%%
tag := "exercises-11"
%%%

{exercise "exr-while-derivation"}[] Build on paper the derivation of `int i = 0; while (i < 2) { i = i + 1; } return i;` and count the applications of each rule of `while`.

{exercise "exr-break"}[] Add `break` to Core C++. Give the control result it produces, the rules of `Seq`, `If` and `While` that handle it, and the typing rule that rejects it outside a loop.

{exercise "exr-do-while"}[] Write the rules of `do {c} while (e);` without using the rules of `while`, and then show how to define it through `while` and a block, as `for` is defined.

{exercise "exr-for-scope"}[] In `for (int i = 0; i < n; i = i + 1) { int i = 5; s = s + i; }`, say which `i` each occurrence denotes, with the rule `For` and the block of the body. Then say what the program computes.

{exercise "exr-if-int"}[] C++ accepts `if (x) { … }` with `x` an `int`, and Core C++ rejects it. Write the rule C++ applies, name the conversion, and explain what the rejection buys.

{exercise "exr-return-void"}[] A `void` function may end without `return`. Say which rule gives its call the value `void`, and what happens, by the rules, when an `int` function ends without `return`.

```lean -show
end Lecture11
```
