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

#doc (Manual) "Lecture 23: Subtyping" =>

%%%
tag := "lecture-23"
%%%

```lean -show
namespace Lecture23
open CoreCpp
```

Inheritance appeared in {secref}[lecture-19] as a way of sharing the members of a class, and it brought with it a conversion, a pointer to a derived class where a pointer to the base is expected. This lecture takes that conversion as what it is, the rule of *subtyping*, and asks the questions the rule raises. Where does it hold, what does it cost at run time, how does it sit beside the parametric polymorphism of {secref}[lecture-22], and why do the two refuse to compose.

*This lecture is also available as [presentation slides](../slides/lecture-23.en.html).*

# Subsumption

%%%
tag := "subsumption-rule"
%%%

A type τ is a *subtype* of a type τ' when an expression of type τ may stand wherever one of type τ' is expected. In Core C++ the relation holds between pointers to classes of one chain, and the rule that states it is called subsumption.

```
Γ ⊢ e : D*    D derives from B
─────────────────────────────── (T-Sub)
Γ ⊢ e : B*
```

The rule reads from the specific to the general. Whoever has a pointer to a `Quadrado` has a pointer to a `Forma`, because every `Quadrado` is a `Forma`. The converse fails, and the type checker says so.

```lean (name := notSuper)
def notSuper : String :=
  "class Forma { public: int lado; };
  class Quadrado : public Forma { public: int marca; };
  int main() { Forma* f = new Quadrado(); Quadrado* q = f; return 0; }"

#eval (parseProgram notSuper).map check
```
```leanOutput notSuper
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of q"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Quadrado"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Forma"))))
```

Subsumption is not a separate judgment. It lives inside the relation τ ≈ τ' that the earlier units used for declarations, assignments, arguments, results, comparisons and the branches of a conditional, so it holds in all of them at once. {numref}[tbl-subsumption] lists the positions.

:::table +header
*
  * Position
  * Rule
  * Example with `D` derived from `B`
*
  * declaration
  * T-Decl
  * `B* b = new D();`
*
  * assignment
  * T-Assign
  * `b = d;`
*
  * argument
  * T-Call
  * `f(d)` with `f(B* x)`
*
  * result
  * T-Ret
  * `return d;` in a function of result `B*`
*
  * comparison
  * T-Eq
  * `b == d`
*
  * branches
  * T-Cond
  * `c ? b : d`
:::

{tabcap "tbl-subsumption"}[The positions where subsumption holds, all through the relation τ ≈ τ'.]

At run time the conversion does nothing. A pointer value is a location, and the location of a `Quadrado` is the location of a `Quadrado` whether the expression that names it has type `Quadrado*` or `Forma*`. The object in the store keeps its class tag, which is why the dispatch of {secref}[lecture-19] can find the method of the derived class through a pointer to the base. Subsumption is a statement about types and costs nothing at run time, exactly as instantiation does, and for the same reason, it happens in Γ.

```lean (name := dispatch)
def dispatch : String :=
  "class Forma {
  public:
    virtual int area() { return 0; }
    virtual ~Forma() { }
  };
  class Quadrado : public Forma {
  private:
    int lado;
  public:
    Quadrado(int l) { this->lado = l; }
    int area() override { return lado * lado; }
  };
  int soma(Forma& f, Forma& g) { return f.area() + g.area(); }
  int main() {
    Forma* a = new Quadrado(3);
    Forma* b = new Quadrado(4);
    int r = soma(*a, *b);
    delete a;
    delete b;
    return r;
  }"

#eval (parseProgram dispatch).map run
```
```leanOutput dispatch
Except.ok (Except.ok (CoreCpp.Val.int 25))
```

The function `soma` knows only `Forma`, and it reaches the `area` of `Quadrado` through the tag. A function that serves every subtype of a type without knowing them is the practical gain of subtyping, and it is what the literature calls *inclusion polymorphism*.{margin}[L. Cardelli and P. Wegner, *On Understanding Types, Data Abstraction, and Polymorphism*, ACM Computing Surveys 17(4), 1985, pp. 471 to 523.]

# Two Kinds of Polymorphism

%%%
tag := "two-kinds"
%%%

The course has now met three ways in which one piece of program serves several types, and they differ in what varies and in when the choice is made. {numref}[tbl-polymorphism] sets them side by side.

:::table +header
*
  * Kind
  * What varies
  * Chosen
  * In Core C++
*
  * overloading
  * the declaration that runs
  * at compile time, by the argument types
  * an overload set in Γ
*
  * parametric
  * the type the declaration serves
  * at compile time, by the instantiation
  * a class template expanded by substitution
*
  * inclusion
  * the method that runs
  * at run time, by the class tag
  * a `virtual` method reached through a pointer to the base
:::

{tabcap "tbl-polymorphism"}[Three kinds of polymorphism, and where each one decides.]

The three answer different questions. Overloading gives one name to operations that do analogous things to unrelated types, and the bodies have nothing in common. Parametric polymorphism gives one body to a family of types, and the body does not look at the type at all. Inclusion polymorphism gives one interface to a family of classes, and each class brings its own body, chosen while the program runs.

Only the third costs anything at run time, the indirection of the dispatch, and only the third can pick a behaviour that depends on a value computed while the program runs.

# Where the Two Do Not Compose

%%%
tag := "variance"
%%%

A natural question follows from the two tables. If `Quadrado*` is a subtype of `Forma*`, is `Pilha<Quadrado*>` a subtype of `Pilha<Forma*>`. The answer in Core C++, as in C++ and Java, is no. Two instantiations of one template are two unrelated classes, and the type checker treats them as it treats `Ponto` and `Conta`.

```lean (name := invariance)
def invariance : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
    void guarda(T x) { v = x; }
  };
  class Forma { public: int lado; };
  class Quadrado : public Forma { public: int marca; };
  int main() {
    Caixa<Quadrado*>* c = new Caixa<Quadrado*>(new Quadrado());
    Caixa<Forma*>* d = c;
    return 0;
  }"

#eval (parseProgram invariance).map check
```
```leanOutput invariance
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Caixa<Forma*>"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Caixa<Quadrado*>"))))
```

The refusal is not a limitation of the implementation, it protects the program. Suppose the conversion were allowed, so that `d` and `c` named one object of class `Caixa<Quadrado*>`. The type of `d` says that `d->guarda(x)` accepts any `Forma*`, so a program could store a `Forma` that is not a `Quadrado` in a box whose `abre` promises a `Quadrado*`, and the next `c->abre()->marca` would read a field of an object that has none. The store would hold an object whose tag contradicts the type of the expression that reaches it, which is exactly what a type system exists to prevent.

The general statement belongs to the theory of subtyping. A parameter that appears only in results may vary with the subtype relation, *covariance*, one that appears only in parameters must vary against it, *contravariance*, and one that appears in both, as `T` does in `Caixa`, may not vary at all, *invariance*. C++ and Core C++ make every instantiation invariant, which is the safe choice and needs no analysis of where the parameter occurs. Java allows the programmer to ask for variance at the use, with the wildcards `? extends` and `? super`, and Scala and Kotlin allow it at the declaration.{margin}[A. Igarashi and M. Viroli, *On Variance-Based Subtyping for Parametric Types*, ECOOP 2002, LNCS 2374, Springer, pp. 441 to 469.]

One place in C++ does allow covariance, the result type of a redefined method, where a `Forma* clona()` may be redefined as `Quadrado* clona()`. Core C++ requires the signature of a redefinition to be equal, so it leaves this case out, and a program of the subset writes the base result type in both.

# Exercises

%%%
tag := "exercises-23"
%%%

{exercise "exr-sub-positions"}[] For each line of {numref}[tbl-subsumption], write a small program of the subset where subsumption is what makes the line type check, and check each one with the type checker.

{exercise "exr-sub-runtime"}[] Print the derivation of the program of {secref}[subsumption-rule] and point to the step where the conversion from `Quadrado*` to `Forma*` happens. Explain the answer.

{exercise "exr-sub-array"}[] Java allows `Quadrado[]` where `Forma[]` is expected, and checks at each store whether the value fits the actual array, throwing an exception otherwise. Say which of the two decisions, the Java one and the Core C++ one, you would take for the subset, and what the other one would cost in the rules.

{exercise "exr-variance-counterexample"}[] Write, in comments over a program of the subset, the sequence of calls that would corrupt the store if `Caixa<Quadrado*>` were a subtype of `Caixa<Forma*>`. Say which rule would have to change to allow it.

{exercise "exr-variance-readonly"}[] Give a template whose parameter appears only in results, and argue in two sentences why the conversion would be harmless for it.

{exercise "exr-covariant-result"}[] Try to redefine a method with a more derived result type, run the type checker, and say what would have to be added to `T-Class` to accept it.

```lean -show
end Lecture23
```
