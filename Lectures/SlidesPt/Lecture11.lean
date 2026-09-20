/-
Slides da Aula 11. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Comandos e Controle" =>

Sequência, bloco, seleção, repetição e o resultado de controle

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-11___-Comandos-e-Controle/)

```lean -show
namespace Slides11
open CoreCpp
```

# §11.1 Sequência e o resultado de controle

```tree
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁
```

* Ambiente e memória fluem de cada comando ao seguinte.

* O *resultado de controle* r é `normal` ou `ret v`. Não é valor da linguagem, nenhuma expressão o observa.

* Dá ao `return` um significado *sem salto*.

# §11.2 Bloco

```tree
ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ', σ'
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ' ∖ (ρ' ∖ ρ)
```

* O controle *passa*, um `return` em um bloco retorna da função.

* ρ é *restaurado*, os nomes do bloco não são visíveis depois dele. Escopo.

* σ perde as posições *próprias* de ρ' ∖ ρ, as variáveis do bloco deixam de existir. Tempo de vida.

* Todo ramo, todo corpo de laço, todo corpo de função é um bloco. O escopo é sempre delimitado por chaves.

# §11.3 Seleção

```tree
ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c₁} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-T)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂

ρ, σ ⊢ e ⇒ bool false, σ₁    ρ, σ₁ ⊢ {c₂} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-F)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂
```

* O ramo parte da memória que a condição produziu.

* `if` sem `else` tem segundo bloco vazio. A condição é `bool`, condição `int` é erro de tipo.

# §11.3 A derivação de uma seleção

```lean (name := ifRun)
def halve : String :=
  "int main() {
     int x = 2;
     if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
     return x;
   }"

#eval (parseProgram halve).map run
```
```leanOutput ifRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ x % 2 == 0 ⇒ true, {ℓ0 ↦ 2}   (Binary)
      ...
    [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ { x = x / 2; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
  [x ↦ ℓ0], {ℓ0 ↦ 2} ⊢ if (x % 2 == 0) { x = x / 2; } else { x = x - 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (If)
```

* O bloco escolhido aparece, o outro não.

# §11.4 Repetição

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

* n iterações encaixam n aplicações de `While-T` e uma de `While-F`. Um laço que nunca termina *não tem derivação*.

# §11.4 Um return dentro de um laço

```lean (name := whileRet)
def untilSeven : String :=
  "int main() {
     int i = 0;
     while (true) {
       i = i + 1;
       if (i == 7) { return i; }
     }
   }"

#eval (parseProgram untilSeven).map run
```
```leanOutput whileRet
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

* `Return` produz `ret 7`, `If-T` o deixa passar, `Seq-Ret` para o corpo, `While-Ret` para o laço, `Call` o consome. Quatro regras, nenhum salto.

# §11.4 O laço for

```tree
ρ, σ ⊢ c₀ ⇒ normal, ρ₀, σ₀    ρ₀, σ₀ ⊢ while (e) { {c} cₛ } ⇒ r, ρ₀, σ₁
────────────────────────────────────────────────────────────────────── (For)
ρ, σ ⊢ for (c₀; e; cₛ) {c} ⇒ r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)
```

* Definido pelo `while`. O inicializador executa uma vez, a sua variável tem o laço como escopo.

* O corpo é um bloco próprio, o passo executa depois dele, fora do escopo do corpo.

* A conclusão libera a variável do laço, com a leitura de posse de `Block`.

# §11.5 Controle sem saltos

* Sem `break`, `continue`, `goto`, exceções. Sai‑se de um laço pela condição ou por `return`.

* Cada construção ausente é uma *transferência de controle não local*, e exige um resultado de controle novo ou continuações.

* `break` como exercício. Um resultado `brk`, passado por `If` e `Seq-Ret`, consumido por `While` como `normal`, rejeitado pelo verificador de tipos fora de um laço.

* Primeiro lugar em que o verificador de tipos precisa saber *em que construção* um comando ocorre.

# Resumo

* A *sequência* leva ρ e σ, e um `ret` a para. O *resultado de controle* substitui os saltos.

* O *bloco* passa o controle, restaura ρ e libera as posições próprias. Escopo e tempo de vida.

* A *seleção* executa um bloco a partir da memória que a condição produziu.

* A *repetição* tem três regras, e `While-T` recorre à própria conclusão. `for` é `while` com um bloco.

* Um `return` dentro de um laço é tratado por quatro regras e nenhum salto.

Exercícios: veja as [notas de aula](../pt/Aula-11___-Comandos-e-Controle/).

```lean -show
end Slides11
```
