/-
Slides da Aula 12. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Expressões com Efeitos Colaterais" =>

Efeitos por chamadas, as ordens de avaliação e a derivação alternativa

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-12___-Express___es-com-Efeitos-Colaterais/)

```lean -show
namespace Slides12
open CoreCpp
```

# §12.1 Efeitos por chamadas

```lean (name := proxDef)
def counter : String :=
  "class Cell { public: int n; };
   int next(Cell* c) {
     c->n = c->n + 1;
     return c->n;
   }
   int main() {
     Cell* c = new Cell();
     return next(c) + 10 * next(c);
   }"

#eval (parseProgram counter).map run
```
```leanOutput proxDef
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* As duas chamadas devolvem 1 e 2. Esquerda primeiro dá 1 + 10 · 2 = 21, direita primeiro dá 2 + 10 · 1 = 12.

* *A ordem faz parte do significado de* `+`.

# §12.2 As ordens que Core C++ fixa

:::table +header
*
  * Construção
  * Ordem
  * Regra
  * C++17
*
  * `e₁ ⊕ e₂`
  * esquerdo, depois direito
  * `Binary`
  * não especificada
*
  * `f(e₁, …, eₖ)`
  * da esquerda para a direita
  * `Call`
  * não especificada
*
  * `e₁ = e₂`
  * direito, depois esquerdo
  * `Assign`
  * fixada
*
  * `e[i]`
  * vetor, depois índice
  * `LocIndex`
  * fixada
*
  * `&&`, `||`, `?:`
  * esquerdo, depois só se preciso
  * `And`, `Or`, `Cond`
  * fixada
:::

* Duas decisões de Core C++, quatro ordens mantidas de C++17. A ordem vive na *ordem das premissas*.

# §12.3 A derivação alternativa

```tree
ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂

ρ, σ ⊢ e₂ ⇒ v₂, σ₁    ρ, σ₁ ⊢ e₁ ⇒ v₁, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary-RL)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

* Um compilador C++ pode aplicar `Binary-RL`. As duas derivações valem para C++17, a norma não escolhe. *Não determinismo*.

* Core C++ tem uma regra e um resultado. `call_order.cpp` devolve 21 aqui, 21 ou 12 sob `g++`.

# §12.3 Atribuição e argumentos

```lean (name := assignOrder)
def assignOrder : String :=
  "class Cell { public: int n; };
   int next(Cell* c) { c->n = c->n + 1; return c->n; }
   int main() {
     Cell* c = new Cell();
     std::vector<int>* v = new std::vector<int>(3);
     (*v)[next(c)] = next(c);
     return (*v)[1] * 10 + (*v)[2];
   }"

#eval (parseProgram assignOrder).map run
```
```leanOutput assignOrder
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

* Lado direito primeiro, `next(c)` vale 1 ali. O índice é avaliado depois e vale 2. O índice 2 recebe 1.

* Argumentos da esquerda para a direita, `f(next(c), next(c))` é `f(1, 2)`.

# §12.4 Por que não proibir efeitos em expressões

* Fidelidade a C++, em que uma chamada dentro de expressão é comum.

* As regras já levam a memória pelas expressões, ρ, σ ⊢ e ⇒ v, σ′, desde a Aula 3. *Nenhuma regra foi reescrita* para admitir efeitos.

* O que as regras fixam é a *ordem*. Um efeito colateral é uma característica que a semântica precisa descrever por completo, e por completo é escolher uma ordem.

# §12.5 O fragmento até aqui

* Tipos `int`, `bool`, `void`, classes com campos, ponteiros, `std::vector<τ>`.

* Expressões com literais, variáveis, operadores, condicional, `new`, acesso a campo, desreferência, indexação, chamadas.

* Comandos com declaração, declaração de referência, atribuição, bloco, `if`, `while`, `for`, `return`.

* Funções com chamada por valor. Vinte e três exemplos concordando com `g++` onde C++ é definido.

* A UD IV acrescenta parâmetros por referência, lambdas e `std::function`, e a chamada por nome com Haskell como contraste.

# Resumo

* Uma expressão tem *efeito colateral* só por uma chamada, e então a *ordem de avaliação* faz parte do seu significado.

* Core C++ fixa toda ordem na ordem das premissas. Esquerda para a direita onde C++17 não especifica, a ordem de C++17 onde ela é fixada.

* A *derivação alternativa* `Binary-RL` é C++ válido e está ausente de Core C++. Uma regra, um resultado.

* Os efeitos ficam na linguagem porque a memória foi levada pelas expressões desde o início.

Exercícios: veja as [notas de aula](../pt/Aula-12___-Express___es-com-Efeitos-Colaterais/).

```lean -show
end Slides12
```
