/-
Slides da Aula 5. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Valores e Tipos" =>

O juízo de tipagem, o contexto Γ e o que um sistema de tipos compra

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-5___-Valores-e-Tipos/)

```lean -show
namespace Slides5
open CoreCpp
```

# §5.1 Valores e tipos

* Um *valor* é um dado que um programa computa, armazena, passa e devolve.

* Um *tipo* é um conjunto de valores com as operações que se aplicam a eles. `int` são os inteiros de 32 bits com aritmética e ordem, `bool` os dois valores de verdade com os conectivos.

* Uma operação sobre um valor fora do seu tipo *não tem significado*. Uma linguagem rejeita o programa, o interrompe, ou deixa a máquina ler os bits.

* Tipos *primitivos* têm valores atômicos, *compostos* constroem valores de valores, *recursivos* contêm a si mesmos.

# §5.1 Os tipos da UD II

:::table +header
*
  * Espécie
  * Tipos
  * Valores
*
  * primitivo
  * `int`, `bool`
  * inteiros de 32 bits, `true`, `false`
*
  * composto
  * `class C` com campos
  * registros de posições, alcançados por `C*`
*
  * recursivo
  * `class No` com um campo `No*`
  * cadeias finitas de registros
*
  * composto
  * `std::vector<int>`
  * sequências de posições, alcançadas por ponteiro
:::

# §5.2 O juízo de tipagem

* Γ ⊢ e : τ, a expressão e tem tipo τ no *contexto* Γ, uma função finita de identificadores em tipos.

* Γ é a contraparte estática de ρ. Uma declaração põe x em Γ, cada uso posterior lê o seu tipo lá. *Sem memória*, os tipos existem antes dos valores.

```tree
─────────────── (T-Lit)      ─────────────── (T-BoolLit)      Γ(x) = τ
Γ ⊢ n : int                  Γ ⊢ b : bool                     ─────────── (T-Var)
                                                              Γ ⊢ x : τ

Γ ⊢ e₁ : int    Γ ⊢ e₂ : int                Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)      ──────────────────────────── (T-Rel)
Γ ⊢ e₁ ⊕ e₂ : int                           Γ ⊢ e₁ ⋈ e₂ : bool
```

# §5.2 Igualdade e condicional

```tree
Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    τ₁ ≈ τ₂    τ₁, τ₂ têm valores
───────────────────────────────────────────────────────── (T-Eq)
Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ tem valores
──────────────────────────────────────────────────────── (T-Cond)
Γ ⊢ e₁ ? e₂ : e₃ : τ
```

* τ₁ ≈ τ₂ é a igualdade até os ponteiros chegarem, depois aceita também `nullptr` diante de um ponteiro.

* "τ tem valores" exclui `void` e, a partir da Aula 6, os *tipos objeto*.

# §5.2 Uma derivação de tipagem

{exh}[x + 1 < 10 com Γ = \[x ↦ int\]]

```tree
  Γ(x) = int
  ────────────── (T-Var)   ────────────── (T-Lit)
  Γ ⊢ x : int              Γ ⊢ 1 : int
  ─────────────────────────────────────── (T-Arith)   ─────────────── (T-Lit)
  Γ ⊢ x + 1 : int                                     Γ ⊢ 10 : int
  ──────────────────────────────────────────────────────────────────── (T-Rel)
  Γ ⊢ x + 1 < 10 : bool
```

# §5.3 Comandos mudam o contexto

```tree
Γ ⊢ e : τ'    τ' ≈ τ    τ tem valores          Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ
─────────────────────────────────── (T-Decl)   ───────────────────────────────── (T-Assign)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                         Γ ⊢ e₁ = e₂ ⊣ Γ

Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂                     Γ ⊢ c₁ … cₙ ⊣ Γ'
────────────────────────── (T-Seq)             ──────────────────── (T-Block)
Γ ⊢ c cs ⊣ Γ₂                                  Γ ⊢ { c₁ … cₙ } ⊣ Γ
```

* Γ ⊢ c ⊣ Γ', o comando está bem tipado e produz o contexto do que segue. Declaração estende, sequência encadeia, bloco descarta.

# §5.3 O verificador em ação

```lean (name := declMismatch)
#eval (parseProgram "int main() { int x = true; return x; }").map check
```
```leanOutput declMismatch
Except.ok (Except.error (CoreCpp.TypeError.mismatch "initialiser of x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

```lean (name := condInt)
#eval (parseProgram "int main() { return 7 / 2 ? 1 : 0; }").map check
```
```leanOutput condInt
Except.ok (Except.error (CoreCpp.TypeError.mismatch "condition" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

* Uma função por juízo, a primeira regra que falha nomeia o erro. C++ converteria a condição inteira, Core C++ não tem essa conversão.

# §5.4 O que um sistema de tipos compra

* Um *sistema de tipos* é o conjunto das regras de tipos com a sua garantia. Em Core C++, toda derivação de programa bem tipado termina em *valor ou em `erro`*, nunca presa.

* `int + bool` não tem regra de avaliação, o sistema de tipos o rejeita *antes* de o avaliador o encontrar.

* `10 / z` tem regra, a que dá `erro`, o sistema de tipos o deixa passar, o divisor é um *valor*.

* *Estático*, antes da execução, para todas as execuções, o que depende de tipos. *Dinâmico*, durante a execução, o que depende de valores.

# §5.4 A fronteira em Core C++

:::table +header
*
  * Situação
  * Verificada
  * Por
*
  * `int` somado a `bool`
  * estaticamente
  * `T-Arith`
*
  * variável fora do escopo
  * estaticamente
  * `T-Var`
*
  * campo que a classe não tem
  * estaticamente
  * `T-Arrow`
*
  * divisão por zero
  * dinamicamente
  * `DivZero`
*
  * desreferência de `nullptr`
  * dinamicamente
  * `LocDeref`
*
  * índice fora do vetor
  * dinamicamente
  * `LocIndex`
:::

* Python verifica tudo dinamicamente. C++ verifica tipos estaticamente, mas aceita conversões e deixa o lado dinâmico indefinido.

# Resumo

* Um *tipo* é um conjunto de valores com operações, e o tipo de uma construção é a primeira parte do seu significado.

* Γ ⊢ e : τ tipa expressões no contexto Γ, a contraparte estática de ρ. Γ ⊢ c ⊣ Γ' encadeia o contexto pelos comandos.

* As regras têm a forma das regras de avaliação, uma por construção, e as derivações são árvores.

* O sistema de tipos garante *nenhuma derivação presa*. O que depende de tipos é verificado estaticamente, o que depende de valores, dinamicamente.

* Core C++ rejeita estaticamente o que pode, e dá `erro` dinamicamente onde C++ é indefinido.

Exercícios: veja as [notas de aula](../pt/Aula-5___-Valores-e-Tipos/).

```lean -show
end Slides5
```
