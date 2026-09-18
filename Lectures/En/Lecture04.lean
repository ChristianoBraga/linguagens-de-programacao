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

#doc (Manual) "Lecture 4: Language Processors" =>

%%%
tag := "lecture-4"
%%%

```lean -show
namespace Lecture4
open CoreCpp
```

This lecture treats the programs that process programs. It distinguishes interpreters from compilers, describes the phases common to both, presents the T diagrams that describe the combination of processors, and examines the Core C++ interpreter as a complete language processor, with its four phases and its four modes of use. The lecture closes Unit I and prepares Unit II, in which type checking gets its rules.

*This lecture is also available as [presentation slides](../slides/lecture-4.en.html).*

# Interpreters and Compilers

%%%
tag := "interpreters-compilers"
%%%

A *language processor* is a program that receives programs of a source language as input. Two kinds matter here.{margin}[D. A. Watt and D. F. Brown, *Programming Language Processors in Java, Compilers and Interpreters*, Prentice Hall, 2000, chapter 2.] An *interpreter* of the language L receives a program in L and its input and executes the program directly, producing its output. A *compiler* from L to a target language M receives a program in L and produces an equivalent program in M, which another processor, often the hardware itself, executes afterwards.

The difference is one of moment, not of essence. The compiler does once, before execution, the analysis work the interpreter redoes at each execution, and for that reason compiled code is usually faster. The interpreter, in exchange, dispenses with the translation step, starts executing at once and can report errors in terms of the source program. Both forms describe the same semantics, and a well defined program produces the same result in both.

Many implementations combine the two forms. CPython compiles each Python module to an intermediate code, the *bytecode*, and a virtual machine interprets that code. The Java virtual machine does the same with the bytecode produced by `javac`, and adds a *just in time* compiler, which translates to machine code, during execution, the fragments executed often. The `g++` compiles C++ to machine code, and the processor executes the result with no intermediary.

# The Phases of a Processor

%%%
tag := "phases"
%%%

Interpreters and compilers share the *analysis* of the source program and differ in what they do after it. {numref}[tbl-phases] lists the phases and what each produces, with the corresponding phase of the Core C++ interpreter.

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
  * `lex`, in `Lexer.lean`
*
  * syntax analysis
  * tokens
  * abstract syntax tree
  * `parseProgram`, in `Parser.lean`
*
  * contextual analysis
  * tree
  * checked tree, with types
  * `check`, in `Typing.lean`
*
  * code generation or evaluation
  * checked tree
  * target program or result
  * `run`, in `Eval.lean`
:::

{tabcap "tbl-phases"}[The phases of a language processor and the functions of the Core C++ interpreter that implement them.]

The three analysis phases form the *front end* of the processor, and depend only on the source language. The final phase is the *back end*, and depends on the target. A compiler for two different machines shares the front end and swaps the back end, and an interpreter is a processor whose back end evaluates the tree instead of translating it. *Contextual analysis*, also called semantic analysis, checks the rules the context free grammar does not express, such as the prior declaration of each identifier and the compatibility of types in each operation. {secref}[lecture-3] showed the judgment Γ ⊢ e : τ that describes it.

# T Diagrams

%%%
tag := "t-diagrams"
%%%

*T diagrams*, proposed by Bratman,{margin}[H. Bratman, *An alternate form of the "UNCOL diagram"*, Communications of the ACM 4(3), 1961, p. 142.] describe processors and their combination. A compiler is a T with the source language on the left, the target language on the right and the language the compiler is written in at the base. An interpreter is a rectangle with the interpreted language on top and the implementation language below. A program is a rectangle with the name of the program on top and its language below. A machine is a triangle with the language it executes.

The Core C++ interpreter is written in Lean. The Lean compiler, in turn, translates Lean to C, and the C compiler of the machine translates C to machine code. The diagram below shows how the interpreter comes to run.

```
  ┌────────────────┐        ┌───────────────┐        ┌───────────────┐
  │   Core C++     │        │ Lean  →  C    │        │  C  →  x86    │
  │  interpreter   │        └───┐       ┌───┘        └───┐       ┌───┘
  ├────────────────┤            │ Lean  │                │  x86  │
  │      Lean      │            └───────┘                └───────┘
  └────────────────┘                                        ▲
                                                            │ runs
                                                        ┌───┴───┐
                                                         ╲ x86 ╱
                                                          ╲   ╱
                                                           ╲ ╱
```

The Lean compiler is written in Lean, which is common in mature languages and is called *self hosting*. To compile the first version of a self hosted compiler one needs an earlier compiler, written in another language or compiled by an earlier version, and the process is called *bootstrapping*. The `g++` is compiled by `g++` itself, and Lean 4 is compiled by Lean 4, from an initial stage in C generated by the previous version.

# The Core C++ Interpreter as a Processor

%%%
tag := "corecpp-processor"
%%%

The interpreter `corecpp` receives a file with a program and a mode of operation, and each mode stops at a different phase. {numref}[tbl-modes] describes them.

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

{tabcap "tbl-modes"}[The four modes of the Core C++ interpreter.]

The mode `run` is the default, and `-` in place of the file reads standard input. The exit code of the process is the value returned by `main` modulo 256, as the operating system does with a compiled program, so the line below behaves like compiling with `g++` and running the result.

```
echo 'int main() { return 42; }' | bin/corecpp -; echo $?
```

A result `error` exits with code 134, that of an aborted process, and a syntax or type error exits with 1. These codes allow comparing, in a script, the interpreter with the compiler on every example of the repository.

Inside the interpreter the phases are chained functions. The function `parseProgram` calls `lex` and the parser. The function `check` walks the tree with the typing context. The function `run` evaluates the tree with the empty environment and store.

```lean (name := checkOk)
def sum : String :=
  "int main() { int x = 1; x = x + 41; return x; }"

#eval (parseProgram sum).map check
```
```leanOutput checkOk
Except.ok (Except.ok ())
```

Contextual analysis detects the use of an identifier outside its scope, which the grammar cannot exclude, because the grammar does not know which names were declared.

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

It also checks the existence of a function `int main()`, without which the program has no entry point.

```lean (name := checkMain)
def noMain : String := "bool main() { return true; }"

#eval (parseProgram noMain).map check
```
```leanOutput checkMain
Except.ok (Except.error (CoreCpp.TypeError.missingMain))
```

# Static and Dynamic Checking

%%%
tag := "static-dynamic"
%%%

A property of a program is checked *statically* when the processor checks it before execution, for all executions at once, and *dynamically* when it checks it during execution, for the execution under way. Contextual analysis is static. The check of an index out of the bounds of a vector is dynamic, because it depends on values computed at run time.

Languages differ in how much they check in each way. Core C++ and C++ check types statically, and a program that adds an `int` to a `bool` is rejected before running. Python checks types dynamically, and the same error only appears when the sum is executed, which may happen after hours of execution or never, if the wrong branch is not reached in the tests.

Core C++ and C++ diverge in what they do with an accepted program. The program below, `type_error.cpp` in the repository, is accepted by `g++`, which converts `true` to 1 and returns 2, and is rejected by the type checker of Core C++, which has no implicit conversions between `bool` and `int`.

```
int main() {
  bool b = true;
  int x = b + 1;
  return x;
}
```

This is the only direction in which the two disagree. Every program Core C++ accepts, `g++` accepts and runs with the same result. A program `g++` accepts may be outside the subset, by using an excluded construction or by depending on a conversion Core C++ lacks.

On the execution side, Core C++ replaces the undefined behaviour of C++ by the result `error`. Division by zero, `int` overflow and access to a freed location are `error` in Core C++ and undefined in C++, where the compiler may produce any result. {numref}[tbl-checking] summarises.

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
  * exception, dynamic
*
  * `2147483647 + 1`
  * `error`, dynamic
  * undefined
  * arbitrary precision integer
*
  * undeclared variable
  * type error, static
  * compilation error
  * exception, dynamic
:::

{tabcap "tbl-checking"}[The same situation in three languages, with the moment at which each detects it.]

# Exercises

%%%
tag := "exercises-4"
%%%

{exercise "exr-t-diagram"}[] Draw the T diagram of the execution of a Python program in CPython, with the compiler to bytecode and the virtual machine, both written in C.

{exercise "exr-bootstrapping"}[] A compiler from L to x86 is written in L, and there exists only a compiler from L to x86 written in C. Draw the T diagrams of the steps until the compiler written in L runs on x86, and explain why the second step produces a more trustworthy compiler than the first.

{exercise "exr-modes"}[] For each example in the `examples/` directory of the repository, predict the exit code of `bin/corecpp run` and compare it with that of compiling with `g++` and running. Explain each difference by the table of {secref}[static-dynamic].

{exercise "exr-phases"}[] Classify each message below by the phase of the interpreter that produces it. "unexpected character '@'", "expected primary expression", "undeclared variable y", "division by zero".

{exercise "exr-static-dynamic"}[] Give an example of a property Core C++ checks dynamically that a language could check statically, and say which information the checker would need for that.

{exercise "exr-accepted-rejected"}[] Write a program accepted by `g++` and rejected by Core C++ that does not use a conversion between `bool` and `int`, and a program accepted by Core C++ whose result under `g++` you can predict by the semantics of {secref}[lecture-3].

```lean -show
end Lecture4
```
