/-
Slides da Aula 8. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Expressões" =>

Ordem de avaliação, curto‑circuito, condicional e o fragmento em Lean

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-8___-Express___es/)

```lean -show
namespace Slides8
open CoreCpp
```

# §8.1 Expressões e comandos

* Uma *expressão* se avalia para um valor. Um *comando* se executa pelo efeito e não tem valor.

* Dois não terminais, `Expr` e `Cmd`, dois juízos, ρ, σ ⊢ e ⇒ v, σ′ e ρ, σ ⊢ c ⇒ r, ρ′, σ′.

* A atribuição é um *comando*. `x = y = 1` não é Core C++. Uma expressão só vira comando com o ponto e vírgula.

* C++ faz da atribuição uma expressão. Core C++ as separa para que *uma expressão tenha efeito só por uma chamada*, e uma chamada só pelos ponteiros que recebe.

# §8.2 A ordem de avaliação importa

```lean (name := ordem)
def ordem : String :=
  "class Cell { public: int n; };
  int next(Cell* c) {
    c->n = c->n + 1;
    return c->n;
  }
  int main() {
    Cell* c = new Cell();
    return next(c) + 10 * next(c);
  }"

#eval (parseProgram ordem).map run
```
```leanOutput ordem
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* Esquerdo primeiro, 1 + 10 · 2. `Arith` encadeia σ no operando esquerdo e σ₁ no direito.

* C++17 deixa a ordem de `+` *não especificada*, um compilador pode computar 21 ou 12. Core C++ tem *uma derivação e um resultado*.

# §8.2 As ordens do fragmento

:::table +header
*
  * Construção
  * Core C++
  * C++17
*
  * `e₁ ⊕ e₂`, `e₁ ⋈ e₂`
  * esquerdo, depois direito
  * não especificada
*
  * `e₁ = e₂`
  * direito, depois esquerdo
  * fixada, a mesma
*
  * `e[i]`
  * vetor, depois índice
  * fixada, a mesma
*
  * `f(e₁, …, eₖ)`
  * argumentos da esquerda para a direita
  * não especificada
*
  * `e₁ && e₂`, `e₁ || e₂`
  * esquerdo, depois direito se preciso
  * fixada, a mesma
*
  * `e₁ ? e₂ : e₃`
  * condição, depois um ramo
  * fixada, a mesma
:::

# §8.3 Curto‑circuito

```lean (name := shortAnd)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z != 0 && 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortAnd
Except.ok (Except.ok (CoreCpp.Val.int 0))
```

```lean (name := shortOr)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z == 0 || 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortOr
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* `And-False` e `Or-True` *não têm premissa* sobre o segundo operando. A divisão por zero nunca roda.

# §8.3 O operando pulado na derivação

```lean (name := traceShort)
#eval match parseProgram "int main() { return 0 != 0 && 10 / 0 > 1; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceShort
ρ₀ = []      σ₀ = {}

  ────────────────── (Lit)    ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 0 ⇒ 0, σ₀          ρ₀, σ₀ ⊢ 0 ⇒ 0, σ₀
  ──────────────────────────────────────────────────── (Binary)
  ρ₀, σ₀ ⊢ 0 != 0 ⇒ false, σ₀
  ───────────────────────────────────────────────────────────── (And)
  ρ₀, σ₀ ⊢ 0 != 0 && 10 / 0 > 1 ⇒ false, σ₀
  ─────────────────────────────────────────────────────────────────── (Return)
  ρ₀, σ₀ ⊢ return 0 != 0 && 10 / 0 > 1; ⇒ ret false, ρ₀, σ₀
  ──────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ false, σ₀
```

* Sob `And` há um filho, nenhuma derivação da divisão.

# §8.4 A expressão condicional

```lean (name := condSkip)
#eval (parseProgram "int main() { int z = 0; return z == 0 ? 42 : 10 / z; }").map run
```
```leanOutput condSkip
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* A contraparte em expressão do `if`. Condição, depois *exatamente um ramo*, `Cond-T` ou `Cond-F`.

* Os ramos têm *um tipo*, `T-Cond`, porque a expressão tem um tipo decida a execução o que decidir.

* É o que faz de `sum` sobre uma lista uma única expressão.

# §8.5 Detalhes da aritmética

```lean (name := truncation)
#eval (parseProgram "int main() { return -7 / 2 * 10 + -7 % 2; }").map run
```
```leanOutput truncation
Except.ok (Except.ok (CoreCpp.Val.int (-31)))
```

* Divisão e resto *truncam em direção a zero*, como C++ fixa. `-7 / 2` é `-3`, `-7 % 2` é `-1`, e `(a / b) * b + a % b = a`.

* Todo resultado passa por `int32`. Fora de 32 bits, `erro`, onde C++ é indefinido. *É isso que faz de `int` um tipo de 32 bits na semântica.*

# §8.6 O fragmento em Lean

:::table +header
*
  * Construção
  * Tipos
  * Avaliação
  * Lean
*
  * literais, variáveis, operadores, condicional
  * `T-Lit` a `T-Cond`
  * `Lit` a `Cond`
  * `Typing.expr`, `Eval.expr`
*
  * `nullptr`, `new C()`, `new std::vector<τ>(n)`
  * `T-Null`, `T-New`, `T-NewVec`
  * `Null`, `New`, `NewVec`
  * `Typing.expr`, `Eval.expr`
*
  * `*e`, `e.f`, `e->f`, `e[i]`
  * `T-Loc…`
  * `Loc…`, `Read`
  * `Typing.lval`, `Eval.lval`
*
  * declaração, atribuição, bloco, laços, `return`
  * `T-Decl` a `T-Ret`
  * `Decl` a `Return`
  * `Typing.cmd`, `Eval.cmd`
*
  * chamada, função, classe, programa
  * `T-Call`, `T-Fun`, `T-Class`, `T-Program`
  * `Call`, `Program`
  * `Typing.fn`, `check`, `runWith`
:::

* Toda regra está no comentário do seu caso, e o [blueprint](https://christianobraga.github.io/corecpp/) liga cada regra ao seu código.

# Resumo

* *Expressões* têm valores, *comandos* têm efeitos. A atribuição é um comando em Core C++.

* Assim que expressões chamam funções com efeitos, *a ordem de avaliação faz parte do significado*. Core C++ fixa da esquerda para a direita onde C++17 não fixa.

* `&&`, `||` e `?:` *pulam* um operando, e o operando pulado pode ser um que seria `erro`.

* A divisão trunca em direção a zero e todo resultado passa por `int32`.

* O fragmento ao fim da UD II. Tipos básicos, classes com campos, ponteiros, vetores, comandos e funções de primeira ordem, *nenhuma regra reescrita* pelas unidades que vêm.

Exercícios: veja as [notas de aula](../pt/Aula-8___-Express___es/).

```lean -show
end Slides8
```
