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

#doc (Manual) "Lecture 15: Lambdas and Closures" =>

%%%
tag := "lecture-15"
%%%

```lean -show
namespace Lecture15
open CoreCpp
```

This lecture makes abstractions into values. A lambda expression `[=](…) -> τ { … }` denotes a function without a name, and its value is a *closure*, the body together with copies of the variables it uses. A closure is stored in a variable of type `std::function`, passed as an argument, returned from a function and called like a function. The lecture writes the rules of the lambda, of the call through a function value and of the capture by copy, and shows the effect through a captured pointer, the one way a closure changes the store outside itself.

*This lecture is also available as [presentation slides](../slides/lecture-15.en.html).*

# Functions as Values

%%%
tag := "function-values"
%%%

In the units so far a function is a declaration of the program, named once and called by that name. It is not a value, no variable holds it and no argument carries it. The functional paradigm of {secref}[lecture-1] rests on the opposite decision, functions are values like integers, and Core C++ admits that decision in the form C++17 gives it. The type `std::function<τ(τ₁, …, τₖ)>` is the type of function values with parameters of types τ₁ to τₖ and result τ, a variable of that type holds a function value, a parameter of that type receives one, and a function may return one.

The values of these types come from *lambda expressions*. The expression below has one parameter, the result type `int`, and a body that uses `k`, a variable of the enclosing scope.

```
[=](int x) -> int { return k * x; }
```

The `[=]` is the *capture clause*. It says that the variables of the enclosing scope the body uses are copied into the value of the lambda at the moment the lambda is evaluated. C++ also offers `[&]`, capture by reference, and Core C++ excludes it, for a reason {secref}[why-copy] gives.

# Where a Lambda Occurs

%%%
tag := "positions"
%%%

A lambda has no type of its own in Core C++. In C++ every lambda has an anonymous *closure type*, distinct from every other, and `auto f = [=]…` gives `f` that type. Core C++ never forms it. The grammar admits a lambda in exactly three positions, and in each of them a `std::function` type is known, so the lambda is checked against that type and converted to it, as C++ does when a lambda meets a `std::function`.

:::table +header
*
  * Position
  * Example
  * Expected type from
*
  * initialiser of a declaration
  * `std::function<int(int)> f = [=](int x) -> int { … };`
  * the declared type
*
  * argument of a call
  * `aplica([=](int x) -> int { … }, 3)`
  * the parameter type
*
  * expression of `return`
  * `return [=](int x) -> int { … };`
  * the result type of the function
:::

{tabcap "tbl-positions"}[The three positions of a lambda and the type each one supplies.]

The judgment that does the checking is written Γ ⊢ e ◁ τ, read "e is acceptable at type τ". For an expression that is not a lambda it is the ordinary Γ ⊢ e : τ' with τ' ≈ τ. For a lambda it is the rule below.

```
Γ' = Γ marked read only, [x₁ ↦ τ₁, …, xₖ ↦ τₖ]    Γ' ⊢ c ⊣ Γ''    τ, τᵢ with values
──────────────────────────────────────────────────────────────────────────────── (T-Lambda)
Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>
```

The parameter and result types of the lambda must be exactly those of the expected type. The body is checked in a context in which every variable of the enclosing scope is marked *read only*, because the body will see copies, and the parameters of the lambda are ordinary variables. A lambda anywhere else, as an operand or as the initialiser of `auto`, is a syntax error, because the grammar places lambdas only in `ArgExpr`.

```lean (name := autoLambda)
def autoLambda : String :=
  "int main() { auto f = [=](int x) -> int { return x; };
   return f(1); }"

#eval parseProgram autoLambda
```
```leanOutput autoLambda
Except.error "syntax error at token 8 ('[=]'): expected primary expression"
```

# The Closure

%%%
tag := "closure"
%%%

The value of a lambda is a closure. It holds the parameters, the result type, the body and one copy per variable of the enclosing scope that the body mentions, taken from the store at the moment of evaluation.

```
{y₁, …, yₘ} = free variables of c bound in ρ, minus the xᵢ
ρ(yⱼ) = ℓⱼ    ℓⱼ ∈ dom σ    wⱼ = σ(ℓⱼ)
──────────────────────────────────────────────────────────────────────────────── (Lambda)
ρ, σ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ⇒ closure(x⃗, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ
```

The store does not change, the lambda only reads it. The closure holds *values*, not locations. That is the meaning of capture by copy, and it has two consequences the programs below make visible. A later write to a captured variable is not seen by the closure. A captured pointer still reaches its object in σ, because the copy of a pointer is the same location.

The program below declares `soma` with `n` equal to 5, then assigns 100 to `n`, and calls `soma`. The closure kept the copy 5.

```lean (name := captureCopy)
def captureCopy : String :=
  "int main() { int n = 5;
   std::function<int(int)> soma = [=](int x) -> int { return x + n; };
   n = 100; return soma(1); }"

#eval (parseProgram captureCopy).map run
```
```leanOutput captureCopy
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

The read only mark of the context rejects a body that writes to a captured variable. The write would change the copy, which C++ also forbids, since the call operator of a `[=]` closure is `const`.

```lean (name := constCapture)
def constCapture : String :=
  "int main() { int n = 1;
   std::function<int()> f = [=]() -> int { n = 2; return n; };
   return f(); }"

#eval (parseProgram constCapture).map check
```
```leanOutput constCapture
Except.ok (Except.error (CoreCpp.TypeError.constCapture "n"))
```

# Calling a Function Value

%%%
tag := "callfn"
%%%

A call through a function value evaluates the function expression to a closure, then the arguments left to right, then allocates fresh locations for the captured copies and for the parameters, and runs the body in an environment that holds *only those bindings*. Nothing of the environment of the call is visible inside, exactly as for a named function. On return the copies, the parameters and the locals of the body leave the store.

```
ρ, σ ⊢ e ⇒ closure(x₁ … xₖ, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ₀
ρ, σ₀ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ
(ℓ'ⱼ, ·) = alloc(wⱼ)    (ℓᵢ, ·) = alloc(vᵢ)
ρ_c = [y₁ ↦ ℓ'₁, …, yₘ ↦ ℓ'ₘ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_c, σ' ⊢ c ⇒ ret v, ρ'', σ''
──────────────────────────────────────────────────────────────────────────────── (CallFn)
ρ, σ ⊢ e(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓ'ⱼ, ℓᵢ} ∪ (ρ'' ∖ ρ_c))
```

When the callee is a variable `f` of function type, the call `f(…)` is this rule, and not the call of a function named `f`. A local variable hides a function of the same name, as in C++. The typing rule requires a function type and checks each argument at the corresponding parameter type, with ◁, so a lambda may itself be an argument.

```
Γ ⊢ e : std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ for each i
──────────────────────────────────────────────────────────── (T-CallFn)
Γ ⊢ e(e₁, …, eₖ) : τ
```

The trace below shows a closure being created, stored in `f`, read back and called. The body runs under \[n ↦ ℓ2, x ↦ ℓ3\], two fresh locations, the copy of `n` and the parameter, and after the call both have left the store.

```lean (name := lambdaTrace)
def lambdaTrace : String :=
  "int main() { int n = 2;
   std::function<int(int)> f = [=](int x) -> int { return x + n; };
   return f(40); }"

#eval match parseProgram lambdaTrace with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput lambdaTrace
    [], {} ⊢ 2 ⇒ 2, {}   (Lit)
  [], {} ⊢ int n = 2; ⇒ normal, [n ↦ ℓ0], {ℓ0 ↦ 2}   (Decl)
    [n ↦ ℓ0], {ℓ0 ↦ 2} ⊢ [=](int x) -> int { return x + n; } ⇒ closure(int x)[n ↦ 2], {ℓ0 ↦ 2}   (Lambda)
  [n ↦ ℓ0], {ℓ0 ↦ 2} ⊢ std::function<int(int)> f = [=](int x) -> int { return x + n; }; ⇒ normal, [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Decl)
        [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f ⇒ₗ ℓ1, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (LocVar)
      [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f ⇒ closure(int x)[n ↦ 2], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Var)
      [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ 40 ⇒ 40, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Lit)
            [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x ⇒ₗ ℓ3, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (LocVar)
          [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x ⇒ 40, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Var)
            [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ n ⇒ₗ ℓ2, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (LocVar)
          [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ n ⇒ 2, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Var)
        [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x + n ⇒ 42, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Binary)
      [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ return x + n; ⇒ ret 42, [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Return)
    [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f(40) ⇒ 42, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (CallFn)
  [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ return f(40); ⇒ ret 42, [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Return)
[], {} ⊢ main() ⇒ 42, {}   (Call)
```

# Higher Order Functions

%%%
tag := "higher-order"
%%%

A function that receives or returns a function value is a *higher order function*. The function `multiplicador` below returns a lambda that captured its parameter `k`, and `aplica` receives a function value and calls it. The composition computes 3 times 14.

```lean (name := multiplicador)
def multiplier : String :=
  "std::function<int(int)> multiplicador(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int aplica(std::function<int(int)> f, int v) { return f(v); }
   int main() { return aplica(multiplicador(3), 14); }"

#eval (parseProgram multiplier).map run
```
```leanOutput multiplicador
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

The closure returned by `multiplicador` outlives the call that created it. Its copy of `k` is a value inside the closure, so nothing points to a location that has left the store. This is why capture by copy is safe in a language whose locals die with their block.

A lambda may be an argument directly, checked against the parameter type of the callee.

```lean (name := duasVezes)
def twice : String :=
  "int duasVezes(std::function<int(int)> f, int x) { return f(f(x)); }
   int main() { return duasVezes([=](int x) -> int { return x * x; }, 3); }"

#eval (parseProgram twice).map run
```
```leanOutput duasVezes
Except.ok (Except.ok (CoreCpp.Val.int 81))
```

# Effects Through a Captured Pointer

%%%
tag := "captured-pointer"
%%%

A captured `int` is a copy that the closure can only read. A captured pointer is a copy of a location, and through it the closure reads and writes an object that lives in σ, outside the closure. The function `contador` below creates an object, captures the pointer to it and returns a closure that increments the field. Each call to the closure changes the same object, and the object survives the block of `contador` because objects created with `new` live until the end of the program.

```lean (name := contador)
def counter : String :=
  "class Caixa { public: int valor; };
   std::function<int()> contador() {
     Caixa* c = new Caixa();
     c->valor = 0;
     return [=]() -> int { c->valor = c->valor + 1; return c->valor; };
   }
   int main() { std::function<int()> k = contador();
     int primeiro = k(); return k() + k() + primeiro; }"

#eval (parseProgram counter).map run
```
```leanOutput contador
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

The three calls return 1, 2 and 3, and the sum is 6. The write `c->valor = …` is accepted by the type checker, because it writes to the field of the object, a location reached through the copy of `c`, and not to `c` itself. This is the idiom by which a closure keeps state in Core C++, an object it owns through a captured pointer.

# Why Only Capture by Copy

%%%
tag := "why-copy"
%%%

C++ offers `[&]`, capture by reference. The closure then holds the locations of the captured variables, and a write inside the body changes the variable outside. The trouble appears when the closure outlives the block of the variable. The location has left the store, the closure still holds it, and the next call reads or writes a dead location, undefined behaviour in C++. Core C++ excludes `[&]` for that reason. Every closure holds values, a captured basic value is a copy, and a captured pointer reaches an object that lives as long as the program. No closure of Core C++ can hold a dangling location, and the rule `Lambda` shows why, it reads σ and stores what it read.

The programs that `[&]` would write are written with a pointer to an object, as `contador` does. The object plays the role of the shared variable, and its lifetime is the one that makes sharing safe. {numref}[tbl-captures] contrasts the two.

:::table +header
*
  * Capture
  * The closure holds
  * Write in the body
  * After the enclosing block ends
*
  * `[=]` on an `int`
  * a copy of the value
  * rejected
  * safe, the copy is inside the closure
*
  * `[=]` on a pointer
  * a copy of the location of an object
  * to the object, allowed
  * safe, the object lives in σ
*
  * `[&]`, excluded
  * the location of the variable
  * to the variable
  * undefined in C++
:::

{tabcap "tbl-captures"}[Capture by copy of basic values and pointers, and the excluded capture by reference.]

# Exercises

%%%
tag := "exercises-15"
%%%

{exercise "exr-compose"}[] Write a function `compoe` that receives two values of type `std::function<int(int)>` and returns their composition as a lambda. Explain, by the rule `Lambda`, what the returned closure captures.

{exercise "exr-capture-time"}[] Modify `captureCopy` so that the lambda is evaluated after the assignment `n = 100`, and predict the result before running it.

{exercise "exr-adder-array"}[] Write a function that receives a vector pointer and a `std::function<int(int)>` and applies the function to every element in place. Say which rules of Units II and IV the body uses.

{exercise "exr-two-counters"}[] Call `contador` twice and store the two closures in `k1` and `k2`. Predict the result of `k1() + k1() + k2()` and explain why the two closures do not share state.

{exercise "exr-capture-set"}[] The rule `Lambda` captures the free variables of the body that ρ binds. Write a lambda whose body declares a local with the same name as a variable outside, and explain what is captured and whether the program can observe it.

{exercise "exr-dangling"}[] Write in C++, outside Core C++, a function that returns a `[&]` lambda capturing a local, call it, and explain by the rules of Units III and IV which location the closure holds after the return.

```lean -show
end Lecture15
```
