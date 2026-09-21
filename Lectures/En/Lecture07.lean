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

#doc (Manual) "Lecture 7: Recursive Types and Vectors" =>

%%%
tag := "lecture-7"
%%%

```lean -show
namespace Lecture7
open CoreCpp
```

This lecture builds the recursive types out of the classes of {secref}[lecture-6], with a field that points to an object of the same class, and gives `nullptr` its meaning as the end of a chain. It then adds `std::vector<int>`, the second composite type of the unit, and uses it to state the completeness principle of Watt, the principle that every type should be usable everywhere and every value should be checkable. The dereference of `nullptr` and the index outside the vector are the two runtime errors of the lecture.

*This lecture is also available as [presentation slides](../slides/lecture-7.en.html).*

# Recursive Types

%%%
tag := "recursive"
%%%

A type is *recursive* when its values contain values of the same type. In Core C++ a recursive type is a class with a field of pointer type to the class itself. The class `Node` below is the node of a linked list, with a value and a pointer to the next node.

```
class Node {
public:
  int value;
  Node* next;
};
```

A value of type `Node*` is either `nullptr` or a pointer to a record whose field `next` is again a value of type `Node*`. Every chain is finite, because every record was created by a `new` that ran before, and the end of the chain is `nullptr`. The recursion is in the type, and the store holds only finitely many records.

The literal `nullptr` has an internal type, `nullptr_t`, compatible with every pointer type and with nothing else. It is the reason the relation ≈ of {secref}[lecture-5] exists. A declaration `Node* p = nullptr` types because `nullptr_t ≈ Node*`, and the comparison `p == nullptr` types by `T-Eq`. Its value is `null`.

```
────────────────────────── (T-Null)      ──────────────────────────── (Null)
Γ ⊢ nullptr : nullptr_t                  ρ, σ ⊢ nullptr ⇒ null, σ
```

A function over a recursive type follows the recursion of the type. The sum of a list is zero for `nullptr` and, for a node, the value of the node plus the sum of the rest.

```lean (name := list)
def list : String :=
  "class Node {
  public:
    int value;
    Node* next;
  };
  int sum(Node* p) {
    return p == nullptr ? 0 : p->value + sum(p->next);
  }
  int main() {
    Node* list = new Node();
    list->value = 1;
    list->next = new Node();
    list->next->value = 2;
    return sum(list);
  }"

#eval (parseProgram list).map run
```
```leanOutput list
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

The field `next` of a fresh node is `nullptr`, by the default values of `New`, so the second node ends the list without an explicit assignment. The conditional evaluates only the chosen branch, so the recursive call is not made at the end of the list, and the recursion terminates because every chain is finite.

# The Null Dereference

%%%
tag := "null"
%%%

The rules `LocDeref` and `LocArrow` of {secref}[lecture-6] require the pointer to evaluate to a location. When it evaluates to `null` there is no rule with a location as result, and the result is `error`. This is the first of the two runtime errors of the lecture, and the point where Core C++ and C++ part ways. C++ leaves the dereference of a null pointer undefined, and on most machines the process is killed by the operating system. Core C++ gives it the defined result `error`, which the interpreter reports and which ends the program.

```lean (name := nullDeref)
#eval (parseProgram "class Node { public: int value; Node* next; };
  int main() { Node* p = nullptr; return p->value; }").map run
```
```leanOutput nullDeref
Except.ok (Except.error (CoreCpp.Error.nullDereference))
```

The check is dynamic, because whether a pointer is null depends on the execution. A type system that separates nullable from non nullable pointers moves part of the check to the static side, and Unit VI mentions the languages that do so. In Core C++ the type `Node*` includes `nullptr`, and the programmer tests it, as `sum` does.

# Vectors

%%%
tag := "vectors"
%%%

The type `std::vector<τ>` is the second composite type of the unit, a sequence of elements of type τ with a size fixed at creation. Like every object of Core C++, a vector is created with `new`, lives in the store and is reached through a pointer. The expression `new std::vector<τ>(n)` evaluates the size, allocates one location per element with the default value of τ, then the vector record, and evaluates to a pointer to it. The element type must have values, so a vector holds integers, booleans or pointers, never objects.

```
Γ ⊢ n : int    τ has values
─────────────────────────────────────────── (T-NewVec)
Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*

ρ, σ ⊢ n ⇒ int k, σ₁    k ≥ 0
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, default τ) for 1 ≤ i ≤ k,  σ'₀ = σ₁
(ℓ, σ₂) = alloc(σ'ₖ, vec [ℓ₁, …, ℓₖ])
─────────────────────────────────────────────────────── (NewVec)
ρ, σ ⊢ new std::vector<τ>(n) ⇒ loc ℓ, σ₂
```

The indexing `e[i]` denotes the location of element i of the vector e denotes. Since the vector is reached through a pointer `v`, the element is written `(*v)[i]`, the dereference giving the vector and the index giving the element. The vector is evaluated before the index, the order C++17 fixes for `operator[]`, and the index must fall in $`[0, n)`.

```
Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
───────────────────────────────────── (T-Index)
Γ ⊢ e[i] : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ₁    σ₁(ℓ) = vec [ℓ₀, …, ℓₙ₋₁]
ρ, σ₁ ⊢ i ⇒ int k, σ₂    0 ≤ k < n
──────────────────────────────────────────── (LocIndex)
ρ, σ ⊢ e[i] ⇒ₗ ℓₖ, σ₂
```

Reading and writing an element go through `Read` and `Assign`, as for fields. The program below fills a vector of three elements and sums it with a loop.

```lean (name := vetor)
def vetor : String :=
  "int main() {
    std::vector<int>* v = new std::vector<int>(3);
    (*v)[0] = 1;
    (*v)[1] = 2;
    (*v)[2] = 3;
    int s = 0;
    for (int i = 0; i < 3; i = i + 1) { s = s + (*v)[i]; }
    return s;
  }"

#eval (parseProgram vetor).map run
```
```leanOutput vetor
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

# The Completeness Principle

%%%
tag := "completeness"
%%%

Watt states the *completeness principle* for types.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, section 2.6.] No operation should be arbitrarily restricted in the types of its operands, and every value of a type should be a first class citizen, storable, passable and returnable. The principle has a dynamic counterpart. A value should carry enough information for every operation on it to be checked. A vector that knows its size can check every index, and a vector that does not know it cannot.

The array of C is the standard counterexample. An `int a[3]` does not carry its size, so `a[3]` reads whatever lies after the array in memory, and the C++ standard leaves the result undefined. The vector of C++ carries its size, but its `operator[]` does not check it, for speed, and the standard leaves the access outside the bounds undefined as well. Core C++ takes the vector because it carries its size, and makes the check part of the meaning of `[]`. An index outside the vector is the second runtime error of the lecture.

```lean (name := outOfBounds)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(2);
    return (*v)[2];
  }").map run
```
```leanOutput outOfBounds
Except.ok (Except.error (CoreCpp.Error.outOfBounds 2 2))
```

The size itself is checked at creation. A negative size is `error`, where C++ converts the negative integer to an enormous unsigned size and either throws or exhausts the memory.

```lean (name := negativeSize)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(0 - 1);
    return 0;
  }").map run
```
```leanOutput negativeSize
Except.ok (Except.error (CoreCpp.Error.negativeSize (-1)))
```

On the static side the principle says that pointers and vectors are values like the others. A pointer is stored in a variable, passed to a function, returned from one and compared for equality, and a vector reached through a pointer can be a field of a class, which is how Unit VI builds a stack. The restriction the course keeps, no object by value, is not a restriction on the operations but on the representation, and the principle is satisfied by the pointers.

# Default Values

%%%
tag := "defaults"
%%%

Every field and every element starts with the default value of its type, `0`, `false` or `nullptr`. The program below reads all three defaults from a fresh object, and the meaning of `New` predicts its result before it runs.

```lean (name := campos)
def campos : String :=
  "class Rec { public: int n; bool ok; Rec* next; };
  int main() {
    Rec* r = new Rec();
    return r->n + (r->ok ? 10 : 1) + (r->next == nullptr ? 100 : 0);
  }"

#eval (parseProgram campos).map run
```
```leanOutput campos
Except.ok (Except.ok (CoreCpp.Val.int 101))
```

# Exercises

%%%
tag := "exercises-7"
%%%

{exercise "exr-list-length"}[] Write in Core C++ a function that counts the nodes of a list of `Node`, and a `main` that builds a list of three nodes and returns the count. Run it with the interpreter.

{exercise "exr-list-store"}[] Draw the store after the `main` of {secref}[recursive] has built its two nodes, before the call to `sum`, with one box per location, and mark the records, the fields and the variable.

{exercise "exr-null-static"}[] Explain why the type checker cannot reject `Node* p = nullptr; return p->value;`, and propose a typing rule that would reject it while still accepting the function `sum`.

{exercise "exr-vector-reverse"}[] Write in Core C++ a `main` that creates a vector of five elements, fills it with 1 to 5, reverses it in place with a loop, and returns the first element. Say how many locations the store holds at the end.

{exercise "exr-completeness"}[] For each of the following, say whether it violates the completeness principle and why. A language in which functions cannot return arrays. A language in which arrays do not carry their size. A language in which every value can be compared for equality.

{exercise "exr-index-order"}[] The rule `LocIndex` evaluates the vector before the index. Write a program in which the two orders give different results, using a function with an effect as the index, and say which result C++17 fixes.

```lean -show
end Lecture7
```
