/-
Slides da Aula 9. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Variáveis e Armazenamento" =>

Os seis atributos de uma variável, declaração, atribuição e saída de bloco

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-9___-Vari___veis-e-Armazenamento/)

```lean -show
namespace Slides9
open CoreCpp
```

# §9.1 Duas funções em vez de uma

* Uma função de nomes em valores não expressa dois nomes para uma variável, um nome que sobrevive a um bloco, um objeto que vários ponteiros alcançam.

* A *posição* é o nível intermediário. ρ leva identificadores a posições, σ leva posições a valores.

* *Uma variável é um par*, uma ligação em ρ e uma posição em σ. Ler x é σ(ρ(x)), atribuir a x escreve em ρ(x).

* A declaração estende ρ e aloca em σ. A atribuição muda só σ. A saída do bloco restaura ρ e encolhe σ.

* Os *armazenáveis*, o que uma posição pode guardar, são `int`, `bool` e ponteiros. Um objeto é um registro de posições, nunca armazenável.

# §9.2 Os seis atributos

:::table +header
*
  * Atributo
  * Onde
  * Fixado por
*
  * identificador
  * chave em ρ e Γ
  * declaração
*
  * posição
  * ρ(x)
  * declaração, alloc
*
  * valor
  * σ(ρ(x))
  * inicializador, depois atribuições
*
  * tipo
  * Γ(x)
  * declaração, estático
*
  * escopo
  * comandos com x em ρ
  * o bloco que declara
*
  * tempo de vida
  * ρ(x) em dom σ
  * de alloc à saída do bloco
:::

* Identificador, tipo e escopo são *estáticos*. Posição, valor e tempo de vida são *dinâmicos*, só existem em uma derivação.

# §9.3 Declaração

```tree
Γ ⊢ e : τ'    τ' ≈ τ    τ tem valores
─────────────────────────────────────── (T-Decl)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ v, σ'    (ℓ, σ″) = alloc(σ', v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

* alloc devolve uma posição fora de dom σ. *Posições nunca são reutilizadas.*

* O ambiente de saída leva a ligação aos comandos seguintes.

```lean (name := noInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput noInit
Except.error "syntax error at token 7 (';'): expected '='"
```

# §9.4 Atribuição

```tree
Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ    τ tem valores
───────────────────────────────────────────────────── (T-Assign)
Γ ⊢ e₁ = e₂ ⊣ Γ

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

* Lado direito primeiro, depois a posição do esquerdo, a ordem que C++17 fixa.

* O tipo de uma variável nunca muda.

```lean (name := assignBool)
#eval (parseProgram "int main() { int x = 1; x = true; return x; }").map check
```
```leanOutput assignBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "assignment to x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

# §9.5 Sombreamento

```lean (name := shadowRun)
def shadow : String :=
  "int main() {
     int x = 1;
     { int x = 10; x = x + 1; }
     return x;
   }"

#eval (parseProgram shadow).map run
```
```leanOutput shadowRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* A ligação interna entra na frente de ρ e a busca a encontra primeiro. Duas variáveis, duas posições.

* Na chave de fechamento a ligação interna sai de ρ e ℓ1 sai de σ.

# §9.5 A derivação de um bloco

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int x = 10; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Decl)
      ...
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
    [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x = x + 1; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 11}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int x = 10; x = x + 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
```

* `Block` devolve o ρ externo e uma memória sem ℓ1. Um acesso posterior a ℓ1 seria `erro`.

* C++ também libera o armazenamento, e deixa o acesso posterior *indefinido*.

# Resumo

* Uma variável é uma *ligação em ρ* e uma *posição em σ*. Ler é σ(ρ(x)), atribuir escreve em ρ(x).

* Seis atributos, três estáticos, identificador, tipo e escopo, três dinâmicos, posição, valor e tempo de vida.

* A *declaração* aloca e estende ρ. A *atribuição* escreve em uma posição viva, lado direito primeiro.

* O *sombreamento* é uma segunda ligação para um nome, com posição própria. A saída do bloco remove as duas.

* Posições nunca são reutilizadas, e um acesso a uma posição liberada é `erro`, não indefinido.

Exercícios: veja as [notas de aula](../pt/Aula-9___-Vari___veis-e-Armazenamento/).

```lean -show
end Slides9
```
