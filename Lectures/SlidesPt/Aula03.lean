/-
Slides da Aula 3. Cada seção de nível superior é um slide. As regras e as
derivações são texto preformatado em blocos `tree`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Semântica" =>

Juízos, regras de inferência e a semântica natural de Core C++

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-3___-Sem___ntica/)

{cite}[G. Kahn, *Natural Semantics*, STACS 87, LNCS 247, Springer, 1987.]

```lean -show
namespace SlidesAula3
open CoreCpp
```

# §3.1 Juízos e regras de inferência

* Na dedução natural, um *juízo* é uma afirmação derivável e uma *regra* leva premissas a uma conclusão.

* Uma *derivação* é uma árvore de aplicações de regras, com axiomas nas folhas.

* A semântica natural usa a mesma forma, com juízos sobre *programas*.

* Estilo de sequentes de Kahn. Contexto à esquerda de ⊢, construção à direita, resultado depois de ⇒.

```tree
premissa₁    premissa₂
───────────────────── (Nome)
      conclusão
```

# §3.2 Ambiente, memória e valores

* *Ambiente* ρ, identificadores em *posições* ℓ.

* *Memória* σ, posições em *valores*. O domínio de σ são as posições vivas.

* Valores do subconjunto atual. `int n` de 32 bits e `bool b`.

* *Ler x é ler σ(ρ(x)). Atribuir a x é escrever em ρ(x).*

* Duas variáveis podem denotar a mesma posição, e uma posição pode viver depois do identificador. Referências na UD III, objetos na UD V, *sem reescrever regra alguma*.

# §3.2 Os quatro juízos

:::table +header
*
  * Juízo
  * Leitura
*
  * Γ ⊢ e : τ
  * e tem tipo τ no contexto Γ
*
  * ρ, σ ⊢ e ⇒ v, σ′
  * sob ρ e σ, e avalia para v e produz σ′
*
  * ρ, σ ⊢ e ⇒ₗ ℓ, σ′
  * sob ρ e σ, e denota a posição ℓ
*
  * ρ, σ ⊢ c ⇒ r, ρ′, σ′
  * sob ρ e σ, c produz o controle r, o ambiente ρ′ e a memória σ′
:::

* O controle r é `normal` ou `ret v`. Todo juízo dinâmico admite `erro`, que não é um valor da linguagem.

# §3.3 Literais e variáveis

```tree
─────────────────────────── (Lit)      ──────────────────────── (BoolLit)
ρ, σ ⊢ n ⇒ int32 n, σ                  ρ, σ ⊢ b ⇒ bool b, σ

ρ(x) = ℓ                              ρ, σ ⊢ x ⇒ₗ ℓ, σ    ℓ ∈ dom σ
────────────────────── (LocVar)       ─────────────────────────────── (Var)
ρ, σ ⊢ x ⇒ₗ ℓ, σ                       ρ, σ ⊢ x ⇒ σ(ℓ), σ
```

* `int32` devolve o inteiro quando ele cabe em 32 bits e `erro` fora.

* A posição de uma variável precisa estar *viva*.

# §3.3 Operadores binários

```tree
ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂
──────────────────────────────────────────────── (Arith, ⊕ ∈ {+, −, ×})
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ int32 (n₁ ⊕ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂    n₂ ≠ 0
──────────────────────────────────────────────────────── (Div, ⊘ ∈ {/, %})
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ int32 (n₁ ⊘ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int 0, σ₂
──────────────────────────────────────────────── (DivZero)
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ erro
```

* Esquerdo antes do direito, a escolha de Core C++ onde C++17 não fixa ordem.

# §3.3 Curto‑circuito e uma derivação

```tree
ρ, σ ⊢ e₁ ⇒ bool false, σ₁
──────────────────────────────── (And-False)
ρ, σ ⊢ e₁ && e₂ ⇒ bool false, σ₁

ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
─────────────────────────────────────────────── (And-True)
ρ, σ ⊢ e₁ && e₂ ⇒ v, σ₂
```

{exh}[x + 41 com ρ = \[x ↦ ℓ₀\] e σ = \{ℓ₀ ↦ 1\}]

```tree
  ρ(x) = ℓ₀
  ──────────────── (LocVar)
  ρ, σ ⊢ x ⇒ₗ ℓ₀, σ    ℓ₀ ∈ dom σ
  ──────────────────────────────── (Var)    ─────────────────── (Lit)
  ρ, σ ⊢ x ⇒ int 1, σ                       ρ, σ ⊢ 41 ⇒ int 41, σ
  ─────────────────────────────────────────────────────────────── (Arith)
  ρ, σ ⊢ x + 41 ⇒ int 42, σ
```

# §3.4 Declaração e atribuição

```tree
ρ, σ ⊢ e ⇒ v, σ′    (ℓ, σ″) = alloc(σ′, v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

* A declaração aloca uma posição *nova* e estende ρ. Posições nunca são reutilizadas.

* A atribuição avalia o lado direito *antes* do esquerdo, a ordem que C++17 fixa.

# §3.4 Sequência e bloco

```tree
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁

ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ′, σ′
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ′ ∖ (ρ′ ∖ ρ)
```

* *Escopo* é a restauração de ρ. *Tempo de vida* é a retirada das posições de σ.

* Um `ret` interrompe a sequência e sobe até a chamada.

# §3.4 Laços

```tree
ρ, σ ⊢ e ⇒ bool false, σ₁
──────────────────────────────────────── (While-F)
ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

ρ, σ ⊢ e ⇒ bool true, σ₁   ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂   ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
─────────────────────────────────────────────────────────────────────────────────── (While-T)
ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
────────────────────────────────────────────────────── (While-Ret)
ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂
```

* `While-T` recorre à *própria conclusão*.

# §3.5 A árvore de derivação impressa pelo interpretador

```lean (name := traceAssign)
def soma : String :=
  "int main() { int x = 1; x = x + 41; return x; }"

#eval match parseProgram soma with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceAssign
    [], {} ⊢ 1 ⇒ 1, {}   (Lit)
  [], {} ⊢ int x = 1; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Decl)
        [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ 1, {ℓ0 ↦ 1}   (Var)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ 41 ⇒ 41, {ℓ0 ↦ 1}   (Lit)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x + 41 ⇒ 42, {ℓ0 ↦ 1}   (Binary)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x = x + 41; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 42}   (Assign)
      [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 42}   (LocVar)
    [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ x ⇒ 42, {ℓ0 ↦ 42}   (Var)
  [x ↦ ℓ0], {ℓ0 ↦ 42} ⊢ return x; ⇒ ret 42, [x ↦ ℓ0], {ℓ0 ↦ 42}   (Return)
[], {} ⊢ main() ⇒ 42, {ℓ0 ↦ 42}   (Call)
```

* *Pós‑ordem*, premissas antes da conclusão, indentadas pela profundidade. A raiz é a última linha.

# §3.6 Erro, determinismo e divergência

```lean (name := divZero)
#eval (parseProgram "int main() { return 10 / 0; }").map run
```
```leanOutput divZero
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

* *Progresso*. Toda derivação de um programa bem tipado termina em valor ou em `erro`.

* *Determinismo*. Premissas mutuamente exclusivas, no máximo uma derivação. Em C++, `f() + g()` pode ter dois resultados.

* *Divergência*. `while (true) { }` não tem derivação finita. A semântica indutiva não descreve programas que não terminam.

{cite}[X. Leroy e H. Grall, *Coinductive big-step operational semantics*, Information and Computation 207(2), 2009.]

# §3.7 Semântica estática

```tree
Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)
Γ ⊢ e₁ ⊕ e₂ : int
```

```lean (name := typeError)
def somaBool : String := "int main() { return 1 + true; }"

#eval (parseProgram somaBool).map check
```
```leanOutput typeError
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

* Mesma forma das regras de avaliação, *sem memória*, verificadas antes da execução. A UD II trata os tipos.

# Resumo

* Um *juízo* afirma o que uma construção computa em um contexto, e uma *derivação* é uma árvore de regras.

* *Ambiente* ρ leva identificadores a posições, *memória* σ leva posições a valores. Ler x é ler σ(ρ(x)).

* Expressões avaliam da esquerda para a direita, com curto‑circuito em `&&` e `||`, e a divisão por zero é `erro`.

* Declaração aloca, atribuição escreve, bloco restaura ρ e retira posições de σ, `while` recorre à própria conclusão.

* O interpretador imprime a *árvore de derivação* em pós‑ordem, e a semântica não descreve programas que divergem.

Exercícios: veja as [notas de aula](../pt/Aula-3___-Sem___ntica/).

```lean -show
end SlidesAula3
```
