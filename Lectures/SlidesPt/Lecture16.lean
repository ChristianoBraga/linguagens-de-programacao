/-
Slides da Aula 16. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Avaliação de Parâmetros" =>

Avaliação estrita, passagem por nome, por necessidade, e o fragmento da UD IV

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-16___-Avalia______o-de-Par___metros/)

```lean -show
namespace Slides16
open CoreCpp
```

# §16.1 Avaliação estrita

```lean (name := first)
def first : String :=
  "int first(int a, int b) { return a; }
   int main() { return first(1, 10 / 0); }"

#eval (parseProgram first).map run
```
```leanOutput first
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

* A regra `Call` avalia todo argumento *antes* do corpo. Usado ou não, uma vez, com efeitos e erros.

* C++, Java, Python e Lean são estritas. As exceções embutidas de Core C++ são `&&`, `||` e `?:`.

# §16.2 Passagem por nome

```tree
f ↦ (τ f (τ₁ name x₁) { c })
ρ_f = [x₁ ↦ thunk(e₁, ρ)]                o argumento não avaliado com o seu ambiente
ρ_f, σ ⊢ c ⇒ ret v, ρ', σ'
───────────────────────────────────────── (Call-Name)
ρ, σ ⊢ f(e₁) ⇒ v, σ'

ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Name)    cada leitura avalia e de novo
ρ, σ ⊢ x ⇒ v, σ'
```

* ALGOL 60. Fora do núcleo. ρ levaria um nome a um *thunk*, e uma leitura poderia ter efeitos.

{cite}[P. Naur (ed.), *Revised Report on the Algorithmic Language ALGOL 60*, Communications of the ACM 6(1), 1963.]

# §16.3 Simulando um argumento adiado

```lean (name := primeiroPreguicoso)
def firstLazy : String :=
  "int first(int a, std::function<int()> b) { return a; }
   int main() { int z = 0;
   return first(1, [=]() -> int { return 10 / z; }); }"

#eval (parseProgram firstLazy).map run
```
```leanOutput primeiroPreguicoso
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* O closure é o thunk, as suas cópias são o ambiente ρ₀. O programador escreve o adiamento, `[=]() -> int { … }` na chamada e `b()` em cada uso.

# §16.3 Avaliação repetida

```lean (name := duasVezesEfeito)
def twiceEffect : String :=
  "class Box { public: int value; };
   int applyTwice(std::function<int()> t) { return t() + t(); }
   int main() { Box* c = new Box(); c->value = 0;
     return applyTwice([=]() -> int {
       c->value = c->value + 1; return c->value; }); }"

#eval (parseProgram twiceEffect).map run
```
```leanOutput duasVezesEfeito
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

* Duas chamadas do thunk, dois efeitos, 1 + 2. A *passagem por necessidade*, avaliar uma vez e lembrar, daria 2.

# §16.4 Avaliação preguiçosa em Haskell

```
primeiro :: Int -> Int -> Int
primeiro a b = a

main = print (primeiro 1 (div 10 0))
```

* Haskell avalia *por necessidade*. A divisão nunca executa, o programa imprime 1.

```tree
ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Need)    a ligação passa a x ↦ v
ρ, σ ⊢ x ⇒ v, σ'
```

* Por necessidade igual a por nome só sem efeitos, o que Haskell garante. As linguagens imperativas ficam estritas.

{cite}[S. Peyton Jones, *The Implementation of Functional Programming Languages*, Prentice Hall, 1987.]

# §16.4 As disciplinas

:::table +header
*
  * Disciplina
  * Argumento avaliado
  * Efeitos
  * Linguagem
*
  * estrita, por valor
  * uma vez, antes da chamada
  * uma vez, sempre
  * Core C++, C++, Java, Python, Lean
*
  * por nome
  * a cada leitura
  * repetidos
  * ALGOL 60
*
  * por necessidade
  * na primeira leitura, se houver
  * uma vez, se lido
  * Haskell
*
  * closure como thunk
  * a cada chamada do closure
  * a cada chamada
  * simulação em Core C++
:::

# §16.5 O fragmento da UD IV

:::table +header
*
  * Construção
  * Regras
*
  * passagem por valor, `return`
  * `T-Call`, `Call`, `Return`
*
  * parâmetros por referência `τ& x`
  * `T-Call` com ⊢ₗ, `Call` com ligação de referência
*
  * `std::function<τ(…)>`, lambdas `[=]`
  * `T-Lambda`, `Lambda`
*
  * chamadas de valores de função
  * `T-CallFn`, `CallFn`
*
  * captura por cópia, somente leitura
  * `T-LocVar` com a marca de somente leitura
:::

```lean (name := functionValue)
def functionValue : String :=
  "int main() {
   std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
   std::function<int(int, int)> h = g; return h(10, 3); }"

#eval (parseProgram functionValue).map run
```
```leanOutput functionValue
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

# Resumo

* Core C++ é *estrita*, todo argumento é avaliado uma vez antes da chamada, com `&&`, `||` e `?:` como exceções não estritas.

* A *passagem por nome* reavalia o argumento a cada leitura, a *passagem por necessidade* o avalia uma vez na primeira leitura. Nenhuma está no núcleo.

* Um closure sem parâmetros *simula* um argumento adiado, e mostra os efeitos repetidos da passagem por nome.

* Haskell é preguiçosa e pura, então por necessidade e por nome coincidem lá.

* A UD IV deu a Core C++ passagem por valor e por referência, lambdas, closures e valores de função, cada um com a sua regra.

Exercícios: veja as [notas de aula](../pt/Aula-16___-Avalia______o-de-Par___metros/).

```lean -show
end Slides16
```
