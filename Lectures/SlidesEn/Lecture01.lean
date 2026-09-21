/-
Slides of Lecture 1. Each top level section is a slide. Lean code is
elaborated at build time and coincides with the code of the notes.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Languages and Paradigms" =>

Concepts, paradigms and the core language Core C++

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-1___-Languages-and-Paradigms/)

Structure from D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990.

```lean -show
namespace Slides1
open CoreCpp
```

# §1.1 Why study programming languages?

* Every language fixes decisions about *values, types, memory, control and abstraction*.

* The decisions determine what is easy to express, what the compiler checks and what is left to the programmer.

* Whoever knows the concepts learns a new language in days and recognises, in an error, the rule that explains it.

* Goals of the syllabus. *Illustrate* the concepts and the paradigms that use them. *Compare* the paradigms.

* Focus of the course. The *meaning of each construction*. What does a declaration, an assignment, a loop, a call compute? A *rule* answers. Paradigm comparison is confined to Unit VII.

# §1.1 The seven units

:::table +header
*
  * Unit
  * Topic
  * Concepts
*
  * I
  * Introduction
  * concepts, syntax, semantics, processors
*
  * II
  * Types
  * values, primitive, composite and recursive types
*
  * III
  * Storage and control
  * variables, commands, side effects
*
  * IV
  * Abstraction
  * functions, parameters, strict and lazy evaluation
*
  * V
  * Encapsulation
  * abstract types, objects and classes
*
  * VI
  * Type systems
  * overloading, polymorphism, inference, inheritance
*
  * VII
  * Paradigms
  * imperative, object oriented, functional, logic
:::

# §1.2 Syntax, semantics and pragmatics

* *Syntax*. Which sequences of symbols are programs. Described by a grammar.

* *Semantics*. What each program means. In this course, *natural semantics*, inference rules that say what each construction computes.

* *Pragmatics*. How the language is used, with which tools and for which purposes.

* The separation is the one of logic. Well formed formulas and valuations there, well formed programs and behaviours here.

# §1.3 Watt's concepts

:::table +header
*
  * Concept
  * Question
*
  * Values and types
  * Which data does a program handle and how are they classified?
*
  * Storage
  * How does a program keep and update data?
*
  * Bindings
  * How does a name come to denote a value, a variable or a function?
*
  * Abstraction
  * How does a piece of program get a name and parameters to be reused?
*
  * Encapsulation
  * How is the representation hidden behind an interface?
*
  * Type systems
  * Which errors does the compiler detect before execution?
:::

# §1.3 The concepts in the semantics

* Environment *ρ*, a function from identifiers to locations.

* Store *σ*, a function from locations to values.

* Typing context *Γ*, a function from identifiers to types.

* The three enter the rules from Unit II on. *No rule is rewritten afterwards.* Only new rules enter.

# §1.4 Paradigms

* *Imperative*. Commands that update variables. C, Pascal, the procedural part of C++.

* *Object oriented*. Objects with state and classes that describe them. Inheritance and dynamic dispatch. Smalltalk, Java, the classes of C++.

* *Functional*. Functions in the mathematical sense and expressions that apply them. No update. Haskell, OCaml, Lean.

* *Logic*. Facts and rules, and execution is the search for a proof. Prolog, with the SLD resolution of the logic course.

* A language brings paradigms together. The classification describes the *style it favours*.

# §1.5 The factorial in C++ and in Haskell

::::cols
:::col
{lbl}[Imperative, C++]

```
int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}
```
:::
:::col
{lbl}[Functional, Haskell]

```
fatorial :: Integer -> Integer
fatorial 0 = 1
fatorial n = n * fatorial (n - 1)
```
:::
::::

# §1.5 The factorial in Prolog and in Python

::::cols
:::col
{lbl}[Logic, Prolog]

```
fatorial(0, 1).
fatorial(N, F) :-
  N > 0,
  M is N - 1,
  fatorial(M, G),
  F is N * G.
```
:::
:::col
{lbl}[Imperative without declared types, Python]

```
def factorial(n):
    acc = 1
    for i in range(2, n + 1):
        acc = acc * i
    return acc
```
:::
::::

* The same function, four sets of constructions. The course studies the *meaning of each construction*, and the comparison returns in Unit VII.

# §1.6 Core C++, the core of the course

* A subset of C++17. Every program compiles with `g++ -std=c++17` and produces the same result.

* *No undefined behaviour*. What C++ leaves undefined is excluded by the syntax and the types or becomes the result `error`.

* *Deterministic*. Where C++ admits more than one result, Core C++ fixes one, left to right.

* *LL(1) grammar*, with three lexical conventions that remove the ambiguities of C++.

* Grows along the units. Types and expressions, commands, functions and lambdas, classes, templates.

# §1.6 The factorial in Core C++, executed

```lean (name := factorialCore)
def factorial : String :=
  "int factorial(int n) {
    int acc = 1;
    for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }
    return acc;
  }
  int main() { return factorial(5); }"

#eval (parseProgram factorial).map run
```
```leanOutput factorialCore
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

* The outer `Except` is the parser, the inner one is evaluation.

# §1.7 Lean as the language of the semantics

* Rules go to the board in *natural semantics* and to the computer in *Lean 4*.

* Abstract syntax as an inductive type, analysers as functions, one judgment per function, one rule per case, with the rule in the comment.

* Three moments. *Demonstration* in Unit I. *Laboratory* in Unit III or IV. *Assignment* of the third assessment.

* No Lean proof is required.

* Code at [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp), blueprint at [christianobraga.github.io/corecpp](https://christianobraga.github.io/corecpp/).

# Summary

* A language is a set of decisions about *values, storage, bindings, abstraction, encapsulation and types*.

* *Syntax* says what a program is, *semantics* what it computes, *pragmatics* how it is used.

* Four *paradigms*, imperative, object oriented, functional and logic, each a family of constructions. The course studies the *meaning of each construction*.

* *Core C++* is the core of the course, with no undefined behaviour, deterministic and LL(1).

* The semantics is written as rules and coded in *Lean*, and the interpreter runs the programs of the core.

Exercises: see the [lecture notes](../en/Lecture-1___-Languages-and-Paradigms/).

```lean -show
end Slides1
```
