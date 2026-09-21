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

#doc (Manual) "Lecture 1: Languages and Paradigms" =>

%%%
tag := "lecture-1"
%%%

```lean -show
namespace Lecture1
open CoreCpp
```

This lecture presents the subject of the course, the meaning of the constructions of programming languages, and its method, in which each construction is studied as part of a core language called Core C++, with typing and evaluation rules written in natural semantics and coded in Lean. The lecture organises the constructions by the concepts of Watt{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990.] and ends with one program in four paradigms.

*This lecture is also available as [presentation slides](../slides/lecture-1.en.html).*

# Why Study Programming Languages?

%%%
tag := "why"
%%%

A computer engineer programs in several languages over a career and chooses, or inherits, the language of each project. Each language fixes a set of decisions about values, types, memory, control and abstraction, and those decisions determine what is easy to express, what the compiler checks and what is left to the programmer. Whoever knows the concepts behind the decisions learns a new language in days, reads someone else's program with confidence and recognises, in a runtime error, the rule of the language that explains it.

The course syllabus{margin}[IME, *Plano de Disciplina 09022, Linguagens de Programação*, Pladis 2025.] fixes two goals. To illustrate the concepts that underlie programming languages and the paradigms that use them. To compare the paradigms. The focus of the course is the first goal, taken as a question about meaning. For each construction, a declaration, an assignment, a loop, a function call, a class, the course asks what it computes and answers with a rule. The paradigms enter as the families in which the constructions appear, and their comparison is confined to Unit VII. {numref}[tbl-uds] shows the seven units and the concepts of each.

:::table +header
*
  * Unit
  * Topic
  * Concepts
*
  * I
  * Introduction
  * concepts and paradigms, syntax and semantics, language processors
*
  * II
  * Types
  * values and types, primitive, composite and recursive types, expressions
*
  * III
  * Storage and control
  * variables and update, commands, side effects
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
  * overloading, polymorphism, type inference, inheritance
*
  * VII
  * Paradigms
  * imperative, object oriented, functional, logic
:::

{tabcap "tbl-uds"}[The units of the course and the concepts they cover.]

# Syntax, Semantics and Pragmatics

%%%
tag := "syntax-semantics"
%%%

The description of a programming language has three parts. The *syntax* says which sequences of symbols are programs. The *semantics* says what each program means, that is, what it computes. The *pragmatics* says how the language is used in practice, with which tools and for which purposes.

Syntax is described by a grammar, and {secref}[lecture-2] treats it in detail. Semantics admits several forms of description.{fnref}[semantics] This course uses *natural semantics*, a form of big step operational semantics in which the meaning of each construction is given by inference rules, and {secref}[lecture-3] presents it. Pragmatics runs through the seven units, in the comparison of C++ with Python, Haskell and Prolog.

The separation between syntax and semantics is the one students know from logic.{margin}[Course 09006, Lógica Matemática, IME, 3rd year.] In propositional logic, the syntax defines the well formed formulas and the semantics assigns each formula a truth value under a valuation. In a programming language, the syntax defines the well formed programs and the semantics assigns each program a behaviour.

:::footnotes

{fnAnchor "semantics"}[] The three classical families are operational semantics, which describes execution by transition or evaluation rules, denotational semantics, which maps each construction to a mathematical object, and axiomatic semantics, which describes the effect of a command by assertions on the state before and after it. Nielson and Nielson present the three over one imperative language.{margin}[H. R. Nielson and F. Nielson, *Semantics with Applications, A Formal Introduction*, Wiley, 1992, revised edition of 1999.]

:::

# Concepts

%%%
tag := "concepts"
%%%

Watt organises the study of languages around a few concepts, each present, in some form, in almost every language. {numref}[tbl-concepts] lists them with the question each one answers and the unit that treats it.

:::table +header
*
  * Concept
  * Question
  * Unit
*
  * Values and types
  * Which data does a program handle and how are they classified?
  * II
*
  * Storage
  * How does a program keep and update data during execution?
  * III
*
  * Bindings
  * How does a name come to denote a value, a variable or a function?
  * III
*
  * Abstraction
  * How does a piece of program get a name and parameters to be reused?
  * IV
*
  * Encapsulation
  * How is the representation of a datum hidden behind an interface?
  * V
*
  * Type systems
  * Which errors does the compiler detect before execution?
  * VI
:::

{tabcap "tbl-concepts"}[Watt's concepts, the question each one answers and the unit that treats it.]

A *value* is a datum that can be computed, stored, passed to a function and returned by it. A *type* is a set of values together with the operations that apply to them. A *variable* is a memory location whose content changes during execution. A *binding* associates an identifier with a value, a variable or a function, and the set of bindings in force at a point of the program is the *environment*. An *abstraction* is a piece of program with a name and parameters, such as a function or a procedure. An *abstract data type* exposes operations and hides the representation.

These concepts reappear, under their own names, in the semantics the course adopts. The environment is ρ, a function from identifiers to locations. The store is σ, a function from locations to values. The typing context is Γ, a function from identifiers to types. The three enter the rules from Unit II on and no rule is rewritten afterwards.

# Paradigms

%%%
tag := "paradigms"
%%%

A *paradigm* is a programming style characterised by the concepts it favours. Four paradigms organise Unit VII and run through the course.

The *imperative* paradigm organises the program in commands that update variables. The state of the computation is the store, and control is sequence, selection and repetition. C, Pascal and the procedural part of C++ are imperative.

The *object oriented* paradigm organises the program in objects, which hold state and answer messages, and in classes, which describe objects of one shape. Inheritance and dynamic dispatch let a call choose the method by the receiving object. Smalltalk, Java and the class part of C++ are object oriented.

The *functional* paradigm organises the program in functions, in the mathematical sense, and in expressions that apply them. There is no update of variables, and the value of an expression depends only on the values of its parts. Haskell, OCaml and Lean are functional.

The *logic* paradigm organises the program in facts and rules, and execution is the search for a proof of a query. Prolog is the reference logic language, and students know it from the course on mathematical logic, with SLD resolution.

A language may bring together more than one paradigm. C++ is imperative, object oriented and, with lambdas and `std::function`, functional. Python brings the three together. Classifying a language by paradigm classifies the style it favours, not a restriction of what it allows. For this course a paradigm is, above all, a set of constructions, and each construction is studied by the meaning it has, independently of the paradigm that made it popular.

# One Program in Four Paradigms

%%%
tag := "four-paradigms"
%%%

The factorial of a natural number serves as comparison. The imperative version, in C++, accumulates the product in a variable along a loop.

```
int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}
```

The functional version, in Haskell, defines the function by equations, one for the base case and one for the step, with no variable and no loop.

```
fatorial :: Integer -> Integer
fatorial 0 = 1
fatorial n = n * fatorial (n - 1)
```

The logic version, in Prolog, defines the relation between a number and its factorial by a fact and a rule. The query `factorial(5, F)` asks for an `F` that satisfies the relation, and the interpreter finds it by resolution.

```
fatorial(0, 1).
fatorial(N, F) :-
  N > 0,
  M is N - 1,
  fatorial(M, G),
  F is N * G.
```

The Python version is imperative in form, but without type declarations. The type of `acc` is decided at run time, and a type error only appears when the wrong operation is executed.

```
def factorial(n):
    acc = 1
    for i in range(2, n + 1):
        acc = acc * i
    return acc
```

The four versions compute the same function. They differ in the constructions they use, a loop and an assignment, recursive equations, a relation and a search, a loop without declared types. The course studies the meaning of each of these constructions, and asks, for each one, what it computes and how a rule states it. The comparison between the four styles returns in Unit VII, with the meaning of each construction already in hand.

# Core C++, the Core of the Course

%%%
tag := "core-cpp"
%%%

Instead of describing each concept in a different language, the course introduces them one by one as constructions of a core language, Core C++, a subset of C++17. Every Core C++ program compiles with `g++ -std=c++17` and produces the same result, so every rule the course writes can be confronted with the compiler. The subset obeys three principles.

*No undefined behaviour.* Everything C++17 leaves undefined, such as division by zero, `int` overflow and access to a freed location, is excluded by the syntax and the type checker or has the defined result `error` at run time.

*Deterministic semantics.* Where C++17 admits more than one result, for instance in the evaluation order of the operands of `+`, Core C++ fixes one, left to right.

*LL(1) grammar.* The grammar admits recursive descent parsing with one token of lookahead, with three lexical conventions that remove the ambiguities of C++. {secref}[lecture-2] presents it.

The program below is the factorial in Core C++, equal to the C++ version of {secref}[four-paradigms], with a function `main` that returns the factorial of 5. The interpreter of the course, written in Lean, parses and runs it.

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

The output has two levels. The outer `Except` says that the parser accepted the text, and the inner one says that evaluation ended in a value, the integer 120. A syntax error would appear at the outer level, and a runtime `error`, such as a division by zero, at the inner one. {secref}[lecture-4] examines the interpreter as a language processor.

Core C++ grows along the units. Unit II adds types and expressions, Unit III variables and commands, Unit IV functions and lambdas, Unit V classes and Unit VI templates and overloading. What the course has implemented so far covers basic types, expressions, commands and first order functions, enough for Unit I and for what {secref}[lecture-3] uses.

# Lean as the Language of the Semantics

%%%
tag := "lean"
%%%

The typing and evaluation rules of Core C++ are written on the board in natural semantics and coded in Lean 4.{margin}[L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28, LNCS 12699, Springer, 2021.] Lean is a functional programming language with dependent types and a proof assistant, and the course uses it as a programming language. The abstract syntax is an inductive type, the lexer and the parser are functions, and each judgment of the semantics is a function, with the rule each case implements in its comment. No Lean proof is required.

Lean enters at three moments. In this unit, as a demonstration, with the interpreter running programs and printing derivation trees. In a laboratory session, in Unit III or IV, in which students add a small construction to the interpreter. In the assignment of the third assessment, in which each group chooses a construction, writes its rules on paper, implements it and compares it with `g++`.

The code of the interpreter is in the repository [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp), with a [blueprint](https://christianobraga.github.io/corecpp/) that presents each rule and points to the function that implements it.

# Exercises

%%%
tag := "exercises-1"
%%%

{exercise "exr-classify"}[] Classify each language you have used by the paradigms it favours, and point out one construction of each that belongs to another paradigm.

{exercise "exr-concepts-python"}[] For the Python version of the factorial, give the environment and the store at the end of the third iteration of the loop, with `n = 5`.

{exercise "exr-prolog-query"}[] Write the sequence of queries the Prolog interpreter generates when answering `factorial(3, F)`, with the rule of {secref}[four-paradigms].

{exercise "exr-haskell-negative"}[] The Haskell version does not terminate on a negative argument. Say why and add an equation that returns 1 for negative arguments, without changing the two existing equations.

{exercise "exr-core-cpp-main"}[] Write in Core C++ a function `main` that returns the sum of the integers from 1 to 10 and run it with the interpreter, as in the example of {secref}[core-cpp].

```lean -show
end Lecture1
```
