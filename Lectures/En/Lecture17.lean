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

#doc (Manual) "Lecture 17: Abstract Data Types" =>

%%%
tag := "lecture-17"
%%%

```lean -show
namespace Lecture17
open CoreCpp
```

This lecture opens Unit V with the question of how a program hides the representation of a datum behind the operations that use it. An *abstract data type* is a set of values known only through a signature of operations, and a class with a `public` and a `private` section is the construction C++ offers to write one. The lecture states visibility as a typing rule of Core C++, presents the class table that the type checker keeps, and writes the rule that makes a class well formed. Objects, constructors and method calls receive their evaluation rules in {secref}[lecture-18].

*This lecture is also available as [presentation slides](../slides/lecture-17.en.html).*

# Representation and Signature

%%%
tag := "signature"
%%%

A stack of integers is known by four operations. Create an empty stack of a given capacity, push a value, pop the value pushed last and ask whether the stack is empty. A program that uses a stack needs nothing else, and in particular it does not need to know that the values sit in a vector with a counter for the next free position. The operations form the *signature* of the type, and the vector and the counter form its *representation*.{margin}[B. Liskov and S. Zilles, *Programming with Abstract Data Types*, ACM SIGPLAN Notices 9(4), 1974, pp. 50 to 59.]

Separating the two has a consequence Parnas stated for modules in general.{margin}[D. L. Parnas, *On the Criteria To Be Used in Decomposing Systems into Modules*, Communications of the ACM 15(12), 1972, pp. 1053 to 1058.] Whoever uses the type depends only on the signature, so the representation may change, from a vector to a linked list for instance, without any change to the programs that use it. The signature is a contract, and the representation is a private decision of the implementer.

In Core C++ an abstract data type is a `class` with two sections. The `public` section holds the signature, the methods a client calls, and the `private` section holds the representation, the fields only the methods reach.

```lean (name := stack)
def stack : String :=
  "class Pilha {
  private:
    std::vector<int>* itens;
    int topo;
  public:
    Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
    void empilha(int x) { (*itens)[topo] = x; topo = topo + 1; }
    int desempilha() { topo = topo - 1; return (*itens)[topo]; }
    bool vazia() { return topo == 0; }
  };
  int main() {
    Pilha* p = new Pilha(8);
    p->empilha(1);
    p->empilha(41);
    return p->desempilha() + p->desempilha();
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The client, the function `main`, creates a stack, pushes two values and pops them. It never mentions `itens` or `topo`. The constructor `Pilha(int n)` runs when `new Pilha(8)` creates the object and gives the fields their first values, and each method reads and writes the fields through `this`, or through the bare field name, which inside a method denotes the field of `this`.

# Visibility as a Typing Rule

%%%
tag := "visibility"
%%%

The separation is enforced before the program runs. A client that reaches into the representation is rejected by the type checker, so the contract is not a convention but a rule of the language.

```lean (name := peek)
def peek : String :=
  "class Pilha {
  private:
    std::vector<int>* itens;
    int topo;
  public:
    Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
  };
  int main() { Pilha* p = new Pilha(8); return p->topo; }"

#eval (parseProgram peek).map check
```
```leanOutput peek
Except.ok (Except.error (CoreCpp.TypeError.privateMember "Pilha" "topo"))
```

The rule is a premise on every access to a member. Inside a member body the typing context Γ binds `this` to a pointer to the class, and the *current class* is the class of `this`. A private member declared in class $`K` is visible exactly when the current class is $`K`.

```
C has τ f declared in K    f public or Γ(this) = K*
──────────────────────────────────────────────────── (Visible)
```

Every rule that reaches a member, field access, arrow access and method call, carries this premise. Outside every class Γ has no `this`, so only public members are visible, and inside the methods of $`K` every member of $`K` is. A derived class does not see the private members of its base, because inside its methods `this` has the derived class, not $`K`, the same rule C++ applies.{fnref}[protected]

:::footnotes

{fnAnchor "protected"}[] C++ has a third section, `protected`, whose members are visible in the class and in its derived classes. Core C++ keeps only `public` and `private`, and a derived class reaches the state of its base through the public methods of the base. The design also leaves out `friend` declarations, which grant visibility to a named function or class, and `static` members, which belong to the class rather than to its objects.

:::

# The Class Table

%%%
tag := "class-table"
%%%

The type checker keeps a *class table*, a finite map from class names to declarations. A declaration has an optional base class, its fields and methods with their visibility, at most one constructor and at most one destructor. {numref}[tbl-class-table] lists what the table answers.

:::table +header
*
  * Question
  * Answer
  * Lean
*
  * the chain of a class
  * the class, its base, the base of the base, up to the root
  * `Program.chain`
*
  * the fields of an object
  * every field of the chain, the root base first, with the declaring class
  * `Program.allFields`
*
  * a method of a class
  * the nearest declaration of that name in the chain, with the declaring class
  * `Program.findMethod`
*
  * whether $`D` derives from $`B`
  * $`B` is in the chain of $`D`
  * `Program.subclass`
*
  * a virtual destructor
  * some class of the chain declares one
  * `Program.hasVirtualDtor`
:::

{tabcap "tbl-class-table"}[The questions the class table answers and the functions of `Syntax.lean` that compute them.]

The same table serves the evaluator, which consults it when `new` allocates the fields of an object and when `delete` frees them, and when a method call resolves the method to run. Inheritance and dispatch are the subject of {secref}[lecture-19].

# A Well Formed Class

%%%
tag := "well-formed"
%%%

A class is well formed when its declaration satisfies the rule `T-Class`, a conjunction of checks on the shape of the class and on the bodies of its members.

```
B exists and the chain of C has no cycle
the fields have types with values, well formed, and repeat no field of a base
the members have distinct names
each method that redefines a method of a base finds it virtual there, carries override and keeps the signature
the constructor of B, if any, takes no parameters
[this ↦ C*, x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'   for the body c of each method, of the constructor and of the destructor
───────────────────────────────────────────────────────────────────────────────────────────────────── (T-Class)
⊢ class C : public B { … }
```

The premise on the bodies is the one that matters for the abstract data type. The body of a method is checked under a context that binds `this` to $`C*` and the parameters to their types, with the return type of the method as the type of `return`. A constructor and a destructor have `void` as their return type. Inside these bodies the fields of the class are reachable by the rule `T-VarField` of {secref}[lecture-18], and the private ones are visible because the current class is $`C`.

The premise on the constructor of the base exists because Core C++ has no initialiser lists, the C++ syntax `D() : B(x) { }` that passes arguments to the constructor of the base. The constructors of a chain run from the root base down, the one of the created class with the arguments of `new` and the others with none, so a base with a parameterised constructor cannot be derived from. The premise on redefined methods is the subject of {secref}[lecture-19].

# Representation Invariants

%%%
tag := "invariants"
%%%

A representation usually satisfies a property that every operation preserves, the *representation invariant*. For the stack, the counter `topo` stays between zero and the capacity of the vector, and the values below `topo` are the ones pushed and not yet popped. Visibility is what makes the invariant provable. Since only the methods write the fields, checking that each method preserves the property, assuming it holds on entry, is enough to know that it holds at every point of every client.

Core C++ makes one consequence of a broken invariant visible. The stack above does not check its bounds, and a client that pushes nine values on a stack of capacity eight makes `empilha` write at index eight of a vector of size eight. In C++ that write is undefined behaviour. In Core C++ it is the result `error`, by the rule `LocIndex` of {secref}[lecture-7], and the program stops at the operation that broke the contract. A stack that checks `topo` against the capacity, and reports the overflow to the client through a `bool` result, keeps the invariant by itself.

# Exercises

%%%
tag := "exercises-17"
%%%

{exercise "exr-queue"}[] Write a class `Fila` with the signature of a queue, enqueue, dequeue and empty, over a vector and two counters, with the counters private. State its representation invariant.

{exercise "exr-visibility-derived"}[] Write a class `Base` with a private field and a class `Derivada : public Base` whose method reads that field, run the type checker and explain the message by the rule `Visible`.

{exercise "exr-swap-representation"}[] Rewrite the stack of {secref}[signature] over a linked list of `No` objects instead of a vector, keeping the signature. Check that the function `main` of the example runs without change.

{exercise "exr-invariant-check"}[] Change `empilha` to return a `bool`, false when the stack is full, and explain why the invariant then holds for every client, with the rule that would otherwise produce `error`.

{exercise "exr-class-table"}[] For the classes of {secref}[signature], write the class table as the type checker sees it, and the context Γ under which the body of `desempilha` is checked.

{exercise "exr-tclass"}[] Give a class that violates each premise of `T-Class` in turn, run the type checker on each one and match the message to the premise.

```lean -show
end Lecture17
```
