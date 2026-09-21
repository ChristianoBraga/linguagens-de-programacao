/-
Slides of Lecture 7. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Recursive Types and Vectors" =>

Linked lists, `nullptr`, `std::vector` and the completeness principle

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-7___-Recursive-Types-and-Vectors/)

{cite}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, section 2.6.]

```lean -show
namespace Slides7
open CoreCpp
```

# §7.1 Recursive types

```
class Node {
public:
  int value;
  Node* next;
};
```

* A type is *recursive* when its values contain values of the same type. In Core C++, a class with a field of type *pointer to the class itself*.

* A `Node*` is `nullptr` or a pointer to a record whose `next` is again a `Node*`. Every chain is *finite*, each record came from a `new` that ran before.

* The recursion is in the *type*. The store holds finitely many records.

# §7.1 nullptr

```tree
────────────────────────── (T-Null)      ──────────────────────────── (Null)
Γ ⊢ nullptr : nullptr_t                  ρ, σ ⊢ nullptr ⇒ null, σ
```

* `nullptr` has the internal type `nullptr_t`, compatible with *every pointer type* and nothing else. This is what the relation ≈ is for.

* `Node* p = nullptr` types because `nullptr_t ≈ Node*`. `p == nullptr` types by `T-Eq`.

# §7.1 A function over a recursive type

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

* The second node ends the list because `next` defaults to `nullptr`. The conditional evaluates only the chosen branch, the recursion stops.

# §7.2 The null dereference

```lean (name := nullDeref)
#eval (parseProgram "class Node { public: int value; Node* next; };
  int main() { Node* p = nullptr; return p->value; }").map run
```
```leanOutput nullDeref
Except.ok (Except.error (CoreCpp.Error.nullDereference))
```

* `LocDeref` and `LocArrow` need a *location*. With `null` there is no rule, the result is `error`.

* C++ leaves it *undefined*, the process is usually killed. Core C++ gives a *defined result* that ends the program.

* The check is *dynamic*. A type system with non nullable pointers moves part of it to the static side.

# §7.3 Vectors

```tree
Γ ⊢ n : int    τ has values
─────────────────────────────────────────── (T-NewVec)
Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*

ρ, σ ⊢ n ⇒ int k, σ₁    k ≥ 0
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, default τ) for 1 ≤ i ≤ k,  σ'₀ = σ₁
(ℓ, σ₂) = alloc(σ'ₖ, vec [ℓ₁, …, ℓₖ])
─────────────────────────────────────────────────────── (NewVec)
ρ, σ ⊢ new std::vector<τ>(n) ⇒ loc ℓ, σ₂
```

* A sequence of elements with a size fixed at creation. Created with `new`, in the store, reached through a pointer, *like every object*.

* Elements have values, integers, booleans or pointers, *never objects*.

# §7.3 Indexing

```tree
Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
───────────────────────────────────── (T-Index)
Γ ⊢ e[i] : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ₁    σ₁(ℓ) = vec [ℓ₀, …, ℓₙ₋₁]
ρ, σ₁ ⊢ i ⇒ int k, σ₂    0 ≤ k < n
──────────────────────────────────────────── (LocIndex)
ρ, σ ⊢ e[i] ⇒ₗ ℓₖ, σ₂
```

* `(*v)[i]`, the dereference gives the vector, the index gives the element. Vector before index, the order C++17 fixes.

* `e[i]` *denotes a location*, so `Read` and `Assign` work as for fields.

# §7.3 Summing a vector

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

# §7.4 The completeness principle

* *No operation arbitrarily restricted* in the types of its operands. *Every value first class*, storable, passable, returnable.

* The dynamic counterpart. A value carries enough information for *every operation on it to be checked*.

* The C array `int a[3]` does not carry its size, `a[3]` is undefined. The C++ vector carries it but `operator[]` does not check it, also undefined.

* Core C++ takes the vector *because it carries its size*, and makes the check part of the meaning of `[]`.

# §7.4 Out of bounds and negative size

```lean (name := outOfBounds)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(2);
    return (*v)[2];
  }").map run
```
```leanOutput outOfBounds
Except.ok (Except.error (CoreCpp.Error.outOfBounds 2 2))
```

```lean (name := negativeSize)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(0 - 1);
    return 0;
  }").map run
```
```leanOutput negativeSize
Except.ok (Except.error (CoreCpp.Error.negativeSize (-1)))
```

# §7.5 Default values

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

* `0`, `false`, `nullptr`. The meaning of `New` predicts the result before the program runs.

# Summary

* A *recursive type* is a class with a pointer to itself. Chains are finite and end in `nullptr`, whose type `nullptr_t` is compatible with every pointer.

* Dereferencing `nullptr` is `error`, *dynamic*, where C++ is undefined.

* A *vector* is an object with one location per element, created with `new` and indexed through `(*v)[i]`, which denotes a location.

* The *completeness principle*. Every value first class, every operation checkable. The vector carries its size, the C array does not.

* Out of bounds and negative size are `error`. Fields and elements start with the *default value* of their type.

Exercises: see the [lecture notes](../en/Lecture-7___-Recursive-Types-and-Vectors/).

```lean -show
end Slides7
```
