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

#doc (Manual) "Lecture 24: Type Inference" =>

%%%
tag := "lecture-24"
%%%

```lean -show
namespace Lecture24
open CoreCpp
```

Every type in the programs of the course so far was written by the programmer. This lecture asks how much of that writing a language may take over, and answers for two points of the scale. Core C++ infers the type of a local declaration from its initialiser, which is `auto`, and Haskell infers the type of a whole program with no annotation at all, by the algorithm of Hindley and Milner. The lecture closes Unit VI by running the whole fragment of the unit in one program.

*This lecture is also available as [presentation slides](../slides/lecture-24.en.html).*

# What `auto` Does

%%%
tag := "auto"
%%%

A local declaration with `auto` gives no type. The type checker takes the one of the initialiser and binds the variable to it.

```
Γ ⊢ e : τ    τ has values    τ ≠ nullptr_t
─────────────────────────────────────────── (T-Auto)
Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]
```

The rule is the one of {secref}[lecture-9], and Unit VI adds no case to it. It already reaches the types the unit introduced, because a pointer has values and an instantiation is a class like any other.

```lean (name := autoInst)
def autoInst : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
  };
  int main() {
    auto c = new Caixa<int>(42);
    auto n = c->abre();
    delete c;
    return n;
  }"

#eval (parseProgram autoInst).map run
```
```leanOutput autoInst
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The gain is in the writing, not in the checking. Both variables have a type as definite as if it had been written, and the program that runs is the same. The reader of `auto c = new Caixa<int>(42)` sees the type in the initialiser, which is the case where `auto` helps, and the reader of `auto n = c->abre()` has to look at the declaration of `abre` to know that `n` is an `int`, which is the case where it costs.

Two premises of the rule refuse a declaration. A type with no values, `void` or an object type, cannot be the type of a variable, as the earlier units decided, and `nullptr` has a type of its own that names no variable.

```lean (name := autoNull)
#eval (parseProgram "int main() { auto x = nullptr; return 0; }").map check
```
```leanOutput autoNull
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable x" (CoreCpp.Ty.nullT)))
```

A lambda is refused for another reason. It has no type at all in the subset, as {secref}[lecture-15] decided, so there is no type for `auto` to copy, and the grammar keeps a lambda out of an `auto` declaration.

# Local Inference and Its Limit

%%%
tag := "limit"
%%%

The inference of `auto` is *local*. It looks at one declaration, takes the type of an expression it can already type, and goes no further. It never runs backwards, from a use to a declaration, and it never solves for an unknown type.

The limit shows in the parameters of a function. A function of the subset declares the type of every parameter and of its result, and no rule takes any of them from the body or from a call.

```lean (name := autoParam)
#eval parseProgram
  "auto f(auto x) { return x; }
  int main() { return f(1); }"
```
```leanOutput autoParam
Except.error "syntax error at token 0 ('auto'): expected basic type"
```

C++ has come to admit both forms, the parameter with `auto` since C++20, where it abbreviates a function template, and the result with `auto` since C++14, where it is taken from the `return`. The subset admits neither, because the first is a function template and the second would make the type of a function depend on its body, which the rule `T-Fun` reads in the other direction.

# Inference over a Whole Program

%%%
tag := "hindley-milner"
%%%

At the other end of the scale, a language may ask for no type at all and find the most general one for every expression. Haskell does that, with the algorithm of Hindley and Milner.{margin}[R. Milner, *A Theory of Type Polymorphism in Programming*, Journal of Computer and System Sciences 17(3), 1978, pp. 348 to 375.] The definition below declares nothing.

```
comprimento [] = 0
comprimento (x : xs) = 1 + comprimento xs
```

The algorithm gives each unknown a type variable, walks the definition collecting equations between types, the *constraints*, and solves them by unification. The first equation says the argument is a list, the second that the result is a number, and nothing in the body says what the elements are, so the element type stays a variable. The answer is `comprimento :: [a] -> Int`, read as, for every type `a`, a function from lists of `a` to integers.

The difference from a template is worth stating precisely. The Haskell definition is *one* implementation that works for every `a`, and the compiler checked it once, for all `a` at once, because the body never looks at an element. A `Pilha<T>` is a text expanded once per instantiation, and each expansion is checked on its own. The Haskell type also states what the function requires, nothing at all in this case, while the template states nothing and lets the instantiation fail.

What the algorithm buys is that a program needs no annotation and still has types. What it costs is that the types it can find are limited to a discipline in which a variable stands for one type at a time, and the moment a language admits subtyping, overloading or a parameter used at two types inside one body, the equations stop having a single most general solution. C++ has all three, which is why C++ infers locally and asks the programmer to write the rest, and Haskell has none of them in that form, which is why it infers everything. Haskell recovers overloading by a separate mechanism, the type class, which keeps the constraint in the type instead of resolving it at the call.

{numref}[tbl-inference] puts the two ends and one middle together.

:::table +header
*
  * Language
  * What is inferred
  * What is written
*
  * C, Pascal
  * nothing
  * every type
*
  * Core C++, C++, Java, Rust
  * the type of a local declaration
  * parameters and results
*
  * Haskell, OCaml
  * every type
  * nothing, and an annotation is a check
:::

{tabcap "tbl-inference"}[How much of the typing a language takes over.]

# The Unit in One Program

%%%
tag := "whole-unit"
%%%

The program below uses every construction of Unit VI. A class template with a member that returns a reference, so that indexing denotes a location. An operator member, so that an infix `+` on an object is a method call. Two overloads of one function name. And `auto` on a pointer to an instantiation.

```lean (name := whole)
def whole : String :=
  "template<typename T>
  class Vetor {
  private:
    std::vector<T>* dados;
  public:
    Vetor(int n) { this->dados = new std::vector<T>(n); }
    T& operator[](int i) { return (*dados)[i]; }
    ~Vetor() { delete dados; }
  };
  class Ponto {
  public:
    int x;
    Ponto* operator+(Ponto& o) {
      Ponto* r = new Ponto();
      r->x = x + o.x;
      return r;
    }
  };
  int soma(int a) { return a; }
  int soma(int a, int b) { return a + b; }
  int main() {
    auto v = new Vetor<int>(2);
    (*v)[0] = 20;
    (*v)[1] = soma(20, 2);
    int s = soma((*v)[0]) + (*v)[1];
    Ponto* p = new Ponto();
    p->x = 0;
    Ponto* q = *p + *p;
    int r = s + q->x;
    delete v;
    delete p;
    delete q;
    return r;
  }"

#eval (parseProgram whole).map check
```
```leanOutput whole
Except.ok (Except.ok ())
```

```lean (name := wholeRun)
#eval (parseProgram whole).map run
```
```leanOutput wholeRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

Reading the derivation of the same program shows where each construction went. The instantiation left no trace, because it happened before the run. The overloaded calls appear as ordinary calls, to the function the checker chose. The operator and the indexing appear as method calls.

```lean (name := wholeTrace)
#eval match parseProgram whole with
  | .ok p =>
    IO.println (String.intercalate "\n"
      ((renderTrace (runWith true p).2).splitOn "\n" |>.filter
        fun l =>
          l.endsWith "(MethodLoc)" || l.endsWith "(LocOf)"))
  | .error e => IO.println e
```
```leanOutput wholeTrace
        [this ↦ ℓ1, i ↦ ℓ7], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ7 ↦ 0} ⊢ &(*dados)[i] ⇒ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ7 ↦ 0}   (LocOf)
    [v ↦ ℓ6], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1} ⊢ (*v)[0] ⇒ₗ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1}   (MethodLoc)
        [this ↦ ℓ1, i ↦ ℓ10], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ10 ↦ 1} ⊢ &(*dados)[i] ⇒ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ10 ↦ 1}   (LocOf)
    [v ↦ ℓ6], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1} ⊢ (*v)[1] ⇒ₗ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1}   (MethodLoc)
            [this ↦ ℓ1, i ↦ ℓ11], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ11 ↦ 0} ⊢ &(*dados)[i] ⇒ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ11 ↦ 0}   (LocOf)
          [this ↦ ℓ1, i ↦ ℓ13], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ13 ↦ 1} ⊢ &(*dados)[i] ⇒ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vetor<int>{dados ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ13 ↦ 1}   (LocOf)
```

The rule `MethodLoc` is the call of `operator[]` in a position that asks for a location, and `LocOf` is the `return` of that member, which hands back the location of the element rather than its value. Between them they are the whole content of the sentence "`v[i]` is a method call that returns `int&`", which the design of the language stated and this unit made true.

# Exercises

%%%
tag := "exercises-24"
%%%

{exercise "exr-auto-where"}[] Take a program of Unit V of twenty lines and replace every local type by `auto`. Say for each replacement whether the program became easier or harder to read, and why.

{exercise "exr-auto-refused"}[] Give three declarations with `auto` that the type checker refuses, one per premise of the rule, and match each message to the premise.

{exercise "exr-hm-length"}[] Run the algorithm of Hindley and Milner by hand on the definition of `comprimento`, writing the type variables and the equations you collect, and reach the answer.

{exercise "exr-hm-subtyping"}[] Give a program with two classes in one chain and a function that returns one or the other according to a condition. Say what type the algorithm of Hindley and Milner would try to find for it, and why subtyping gets in the way.

{exercise "exr-whole-unit"}[] Extend the program of {secref}[whole-unit] with a second instantiation of `Vetor` and an overload of `soma` over pointers, run the type checker and the interpreter, and say which lines of the derivation changed.

{exercise "exr-unit-summary"}[] Write, in one page, the four constructions of Unit VI with the rule of each one, and say for each whether it costs anything at run time.

```lean -show
end Lecture24
```
