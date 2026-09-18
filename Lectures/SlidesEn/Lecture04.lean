/-
Slides of Lecture 4. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Language Processors" =>

Interpreters, compilers, phases and T diagrams

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-4___-Language-Processors/)

{cite}[D. A. Watt and D. F. Brown, *Programming Language Processors in Java*, Prentice Hall, 2000, chapter 2.]

```lean -show
namespace Slides4
open CoreCpp
```

# §4.1 Interpreters and compilers

* A *language processor* receives programs as input.

* An *interpreter* of L receives a program in L and its input, and *executes* it.

* A *compiler* from L to M receives a program in L and produces an *equivalent* program in M.

* The difference is one of *moment*. The compiler analyses once, before execution. The interpreter redoes the analysis at each execution and reports errors in terms of the source.

* CPython compiles to bytecode and interprets. The JVM interprets bytecode and compiles *just in time*. The `g++` compiles to machine code.

# §4.2 The phases

:::table +header
*
  * Phase
  * Input
  * Output
  * In Core C++
*
  * lexical analysis
  * characters
  * tokens
  * `lex`
*
  * syntax analysis
  * tokens
  * abstract syntax tree
  * `parseProgram`
*
  * contextual analysis
  * tree
  * checked tree
  * `check`
*
  * generation or evaluation
  * checked tree
  * target program or result
  * `run`
:::

* The first three are the *front end*, they depend only on the source language. The last one is the *back end*, it depends on the target.

# §4.3 T diagrams

```tree
  ┌────────────────┐        ┌───────────────┐        ┌───────────────┐
  │   Core C++     │        │ Lean  →  C    │        │  C  →  x86    │
  │  interpreter   │        └───┐       ┌───┘        └───┐       ┌───┘
  ├────────────────┤            │ Lean  │                │  x86  │
  │      Lean      │            └───────┘                └───────┘
  └────────────────┘                                        ▲
                                                        ┌───┴───┐
                                                         ╲ x86 ╱
                                                          ╲   ╱
                                                           ╲ ╱
```

* A compiler is a T, source on the left, target on the right, implementation language at the base. An interpreter is a rectangle. A machine is a triangle.

* Lean is *self hosted*, compiled by Lean. The first compiler requires *bootstrapping*.

{cite}[H. Bratman, *An alternate form of the "UNCOL diagram"*, Communications of the ACM 4(3), 1961.]

# §4.4 The Core C++ interpreter

:::table +header
*
  * Mode
  * Phases
  * Output
*
  * `ast`
  * lexical and syntactic
  * the abstract syntax tree
*
  * `check`
  * up to contextual
  * acceptance or the type error
*
  * `run`
  * all
  * the value of `main`, also as exit code
*
  * `trace`
  * all
  * the derivation tree and the value of `main`
:::

```
echo 'int main() { return 42; }' | bin/corecpp -; echo $?
```

* The exit code is the value of `main` modulo 256. `error` exits with 134, a syntax or type error with 1.

# §4.4 Contextual analysis

```lean (name := checkScope)
def scope : String :=
  "int main() {
     int x = 1;
     { int y = 2; x = x + y; }
     return y;
   }"

#eval (parseProgram scope).map check
```
```leanOutput checkScope
Except.ok (Except.error (CoreCpp.TypeError.undeclaredVariable "y"))
```

* The grammar does not know which names were declared. Contextual analysis does.

* It also requires `int main()`, the entry point of the program.

# §4.5 Static and dynamic checking

* *Static*, before execution, for all executions. *Dynamic*, during execution, for the execution under way.

* Core C++ and C++ check types statically. Python, dynamically, and the error may appear after hours or never.

:::table +header
*
  * Situation
  * Core C++
  * C++
  * Python
*
  * `1 + true`
  * type error, static
  * accepted, equals 2
  * accepted, equals 2
*
  * `10 / 0`
  * `error`, dynamic
  * undefined
  * exception
*
  * `2147483647 + 1`
  * `error`, dynamic
  * undefined
  * arbitrary precision
:::

# §4.5 The only direction of disagreement

```
int main() {
  bool b = true;
  int x = b + 1;
  return x;
}
```

* `g++` accepts, converts `true` to 1 and returns 2. Core C++ *rejects*, with no implicit conversions between `bool` and `int`.

* Every program Core C++ accepts, `g++` accepts and runs with the *same result*.

* Where C++ is undefined, Core C++ gives `error`.

# Summary

* *Interpreters* execute, *compilers* translate, and many implementations combine both.

* Four *phases*, lexical, syntactic, contextual and generation or evaluation. Front end and back end.

* *T diagrams* describe processors and their combination. Self hosting requires bootstrapping.

* The Core C++ interpreter is a complete processor, with the modes `ast`, `check`, `run` and `trace`.

* *Static* checking before execution, *dynamic* during it. Core C++ replaces the undefined by `error`.

Exercises: see the [lecture notes](../en/Lecture-4___-Language-Processors/).

```lean -show
end Slides4
```
