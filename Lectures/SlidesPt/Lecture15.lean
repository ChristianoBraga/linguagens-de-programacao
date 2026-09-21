/-
Slides da Aula 15. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Lambdas e Closures" =>

Funções como valores, captura por cópia e chamadas por std::function

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-15___-Lambdas-e-Closures/)

```lean -show
namespace Slides15
open CoreCpp
```

# §15.1 Funções como valores

* Até aqui uma função é uma *declaração*, nomeada uma vez, chamada pelo nome, nunca guardada ou passada.

* `std::function<τ(τ₁, …, τₖ)>` é o tipo dos *valores de função*. Uma variável guarda um, um parâmetro recebe um, uma função devolve um.

* Os valores vêm de *expressões lambda*. `[=]` é a cláusula de captura, cópias das variáveis que o corpo usa.

```
[=](int x) -> int { return k * x; }
```

# §15.2 Onde um lambda ocorre

:::table +header
*
  * Posição
  * Tipo esperado vem de
*
  * inicializador, `std::function<int(int)> f = [=]…`
  * o tipo declarado
*
  * argumento, `apply([=]…, 3)`
  * o tipo do parâmetro
*
  * `return [=]…`
  * o tipo de resultado da função
:::

* Sem tipo de closure próprio. O lambda é conferido *com* o `std::function` da sua posição, Γ ⊢ e ◁ τ.

```lean (name := autoLambda)
def autoLambda : String :=
  "int main() { auto f = [=](int x) -> int { return x; };
   return f(1); }"

#eval parseProgram autoLambda
```
```leanOutput autoLambda
Except.error "syntax error at token 8 ('[=]'): expected primary expression"
```

# §15.2 A tipagem de um lambda

```tree
Γ' = Γ marcado somente leitura, [x₁ ↦ τ₁, …, xₖ ↦ τₖ]    Γ' ⊢ c ⊣ Γ''
──────────────────────────────────────────────────────────────────── (T-Lambda)
Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>
```

* Tipos de parâmetros e de resultado *exatamente* os do tipo esperado.

* O corpo vê as variáveis da vizinhança como *somente leitura*, elas serão cópias.

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

# §15.3 O closure

```tree
{y₁, …, yₘ} = variáveis livres de c ligadas em ρ, menos os xᵢ
ρ(yⱼ) = ℓⱼ    ℓⱼ ∈ dom σ    wⱼ = σ(ℓⱼ)
────────────────────────────────────────────────────────────────── (Lambda)
ρ, σ ⊢ [=](x⃗) -> τ { c } ⇒ closure(x⃗, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ
```

* O closure guarda *valores*, copiados no lambda. Uma escrita posterior em `n` não é vista.

```lean (name := captureCopy)
def captureCopy : String :=
  "int main() { int n = 5;
   std::function<int(int)> sum = [=](int x) -> int { return x + n; };
   n = 100; return sum(1); }"

#eval (parseProgram captureCopy).map run
```
```leanOutput captureCopy
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

# §15.4 A chamada de um valor de função

```tree
ρ, σ ⊢ e ⇒ closure(x⃗, τ, c, [y⃗ ↦ w⃗]), σ₀    ρ, σᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ
(ℓ'ⱼ, ·) = alloc(wⱼ)    (ℓᵢ, ·) = alloc(vᵢ)
ρ_c = [y⃗ ↦ ℓ⃗', x⃗ ↦ ℓ⃗]    ρ_c, σ' ⊢ c ⇒ ret v, ρ'', σ''
──────────────────────────────────────────────────────────── (CallFn)
ρ, σ ⊢ e(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓ'ⱼ, ℓᵢ} ∪ (ρ'' ∖ ρ_c))
```

* Posições novas para as cópias e os parâmetros, um ambiente com *só elas*, tudo liberado no retorno.

* `f(…)` com `f` variável de tipo função é esta regra. Uma local esconde a função de mesmo nome.

# §15.5 Funções de ordem superior

```lean (name := multiplier)
def multiplier : String :=
  "std::function<int(int)> multiplier(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int apply(std::function<int(int)> f, int v) { return f(v); }
   int main() { return apply(multiplier(3), 14); }"

#eval (parseProgram multiplier).map run
```
```leanOutput multiplier
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* O closure sobrevive à chamada de `multiplier`. A sua cópia de `k` está *dentro* do closure, nada fica pendente.

# §15.6 Efeitos por um ponteiro capturado

```lean (name := counter)
def counter : String :=
  "class Box { public: int value; };
   std::function<int()> counter() {
     Box* c = new Box();
     c->value = 0;
     return [=]() -> int { c->value = c->value + 1; return c->value; };
   }
   int main() { std::function<int()> k = counter();
     int first = k(); return k() + k() + first; }"

#eval (parseProgram counter).map run
```
```leanOutput counter
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

* A cópia de `c` é a *mesma posição*. O objeto vive em σ, então cada chamada o atualiza. É assim que um closure guarda estado.

# §15.7 Por que só a captura por cópia

:::table +header
*
  * Captura
  * O closure guarda
  * Depois que o bloco termina
*
  * `[=]` em um `int`
  * uma cópia do valor
  * segura
*
  * `[=]` em um ponteiro
  * uma cópia da posição de um objeto
  * segura, o objeto vive em σ
*
  * `[&]`, excluída
  * a posição da variável
  * indefinida em C++
:::

* Nenhum closure de Core C++ pode guardar uma posição pendente. A regra `Lambda` lê σ e guarda o que leu.

# Resumo

* Os tipos `std::function<τ(…)>` têm *closures* como valores, feitos por lambdas `[=]` em três posições.

* Um lambda não tem tipo próprio, é conferido *no* tipo esperado, Γ ⊢ e ◁ τ, com as variáveis da vizinhança somente leitura.

* Um closure guarda *cópias*, tomadas no lambda. Um ponteiro capturado continua alcançando o seu objeto.

* Uma chamada por valor de função aloca cópias e parâmetros de novo e os libera no retorno.

* `[&]` é excluída, então nenhum closure fica pendente.

Exercícios: veja as [notas de aula](../pt/Aula-15___-Lambdas-e-Closures/).

```lean -show
end Slides15
```
