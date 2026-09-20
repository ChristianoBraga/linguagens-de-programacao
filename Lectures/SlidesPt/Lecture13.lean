/-
Slides da Aula 13. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Funções e Passagem por Valor" =>

Abstração, a regra da chamada, cópias e o controle de retorno

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-13___-Fun______es-e-Passagem-por-Valor/)

{cite}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, capítulo 5.]

```lean -show
namespace Slides13
open CoreCpp
```

# §13.1 Abstração

* Uma *abstração* dá nome e parâmetros a um trecho de programa.

* Uma *função* abstrai uma expressão, a sua chamada produz um valor. Um *procedimento* abstrai um comando, a sua chamada tem efeito em σ. Core C++ escreve os dois como funções, `void` para o segundo.

* *Parâmetros* são os nomes que o corpo usa, *argumentos* são as expressões que a chamada fornece. O *mecanismo de passagem* os relaciona.

* A UD I fixou um mecanismo, a *passagem por valor*. Esta unidade escreve a sua regra, acrescenta a passagem por referência, funções como valores, e compara com outras disciplinas.

# §13.2 A regra da chamada

```tree
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })
ρ, σ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ            argumentos, da esquerda para a direita
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, vᵢ),  σ'₀ = σₖ                  uma posição nova com a cópia
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                            só os parâmetros
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓ₁, …, ℓₖ}              as cópias saem
```

* Argumentos primeiro, efeitos mantidos. Depois uma *posição nova* por valor. O corpo vê *só os parâmetros*, não há globais. O retorno libera as cópias.

# §13.2 A tipagem de uma chamada

```tree
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ' com τᵢ' ≈ τᵢ
────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

```lean (name := quadrado)
def square : String :=
  "int quadrado(int n) { return n * n; }
   int main() { int a = 6; return quadrado(a + 1); }"

#eval (parseProgram square).map run
```
```leanOutput quadrado
Except.ok (Except.ok (CoreCpp.Val.int 49))
```

* O argumento `a + 1` é avaliado para 7 antes de o corpo executar.

# §13.3 O parâmetro é uma cópia

```lean (name := dobro)
def double : String :=
  "int dobro(int n) { n = n * 2; return n; }
   int main() { int x = 21; return dobro(x) + x; }"

#eval (parseProgram double).map run
```
```leanOutput dobro
Except.ok (Except.ok (CoreCpp.Val.int 63))
```

* `dobro` escreve em `n`, a cópia em uma posição nova. O `x` de `main` mantém 21, e o resultado é 42 + 21.

* Na árvore o corpo executa sob \[n ↦ ℓ1\], e depois da chamada a memória volta a \{ℓ0 ↦ 21\}.

# §13.4 O return como controle

* `return e` produz o controle *ret v*. `Seq-Ret`, `While-Ret`, `if` e blocos o propagam para cima. Só a chamada o transforma de volta em valor.

* Um corpo que termina com *normal* não retornou. Função `void`, o valor é void. As demais, `erro`.

```lean (name := semRetorno)
def noReturn : String :=
  "int f(int n) { if (n > 0) { return 1; } }
   int main() { return f(0); }"

#eval (parseProgram noReturn).map run
```
```leanOutput semRetorno
Except.ok (Except.error (CoreCpp.Error.missingReturn "f"))
```

* O verificador de tipos não vê isso, precisaria de uma análise de fluxo. C++ deixa indefinido, Core C++ dá `erro`.

# §13.5 Verificação estática das chamadas

```lean (name := callType)
def wrongArgument : String :=
  "int f(int n) { return n; } int main() { return f(true); }"

#eval (parseProgram wrongArgument).map check
```
```leanOutput callType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument n of f" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

* A função existe, a aridade coincide, cada argumento tem o tipo do seu parâmetro, `nullptr` contra ponteiro como única tolerância.

* Dentro do corpo os parâmetros são todo o contexto inicial, e o `return` é conferido com o tipo de resultado, regra `T-Fun`.

# Resumo

* Funções abstraem expressões, procedimentos abstraem comandos, ambos são funções em Core C++.

* *Passagem por valor*. Argumentos da esquerda para a direita, uma posição nova com cópia por parâmetro, um corpo que vê só os parâmetros, cópias liberadas no retorno.

* Uma escrita em um parâmetro nunca alcança o argumento.

* `return` é um *resultado de controle* consumido pela chamada. Um corpo que termina sem ele é `erro`, salvo `void`.

* As chamadas são verificadas estaticamente, aridade e tipos dos argumentos.

Exercícios: veja as [notas de aula](../pt/Aula-13___-Fun______es-e-Passagem-por-Valor/).

```lean -show
end Slides13
```
