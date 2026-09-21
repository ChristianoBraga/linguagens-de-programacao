/-
Slides da Aula 14. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Passagem por Referência" =>

Parâmetros por referência, troca, aliasing e o que C++ deixa indefinido

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-14___-Passagem-por-Refer___ncia/)

```lean -show
namespace Slides14
open CoreCpp
```

# §14.1 Um parâmetro ligado a uma posição

* `void inc(int& r)`. O parâmetro `r` é um nome para a *posição do argumento*, como a referência local `int& y = x` da UD III.

* O argumento precisa denotar uma posição. Uma variável, um campo, `*p`, um elemento de vetor. Não um literal, não um resultado aritmético.

* No ambiente da função a ligação é de *referência*, e o retorno não a libera.

# §14.1 A regra da chamada com os dois mecanismos

```tree
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
para cada i, da esquerda para a direita, σ'₀ = σ,
  pᵢ = τᵢ     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)     por valor
  pᵢ = τᵢ&    ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ                              por referência
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
─────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ por valor} ∪ (ρ' ∖ ρ_f))
```

* Uma premissa difere. ⇒ e alloc para um valor, ⇒ₗ e nenhuma alocação para uma referência. Cópias e locais saem, referentes ficam.

# §14.2 Troca

```lean (name := swap)
def swap : String :=
  "void swap(int& a, int& b) { int t = a; a = b; b = t; }
   int main() { int x = 1; int y = 2; swap(x, y);
     return x * 10 + y; }"

#eval (parseProgram swap).map run
```
```leanOutput swap
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* O ambiente de `swap` é \[a ↦ ℓ0, b ↦ ℓ1\], as posições de `x` e `y` sob nomes novos. As escritas alcançam `main`.

* Por valor o mesmo corpo permutaria duas cópias e devolveria 12.

# §14.3 Qualquer posição é argumento

```lean (name := incField)
def incrementField : String :=
  "class P { public: int a; };
   void inc(int& r) { r = r + 1; }
   int main() { P* p = new P(); inc(p->a); inc(p->a);
     std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
     return p->a * 10 + (*v)[1]; }"

#eval (parseProgram incrementField).map run
```
```leanOutput incField
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

* Um campo e um elemento de vetor denotam posições, e `inc` os altera no lugar.

# §14.3 O que é rejeitado

```lean (name := incLit)
def incrementLiteral : String :=
  "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }"

#eval (parseProgram incrementLiteral).map check
```
```leanOutput incLit
Except.ok (Except.error (CoreCpp.TypeError.refArgument "inc" "r" (CoreCpp.Expr.intLit 5)))
```

```tree
Γ ⊢ eᵢ : τᵢ' com τᵢ' ≈ τᵢ para pᵢ = τᵢ    Γ ⊢ₗ eⱼ : τⱼ para pⱼ = τⱼ&
────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

* O argumento de um parâmetro por referência é conferido com ⊢ₗ e precisa ter *exatamente* o tipo do parâmetro.

# §14.4 Aliasing entre parâmetros

```lean (name := dup)
def duplicate : String :=
  "void dup(int& a, int& b) { a = a + b; b = b + a; }
   int main() { int x = 1; dup(x, x); return x; }"

#eval (parseProgram duplicate).map run
```
```leanOutput dup
Except.ok (Except.ok (CoreCpp.Val.int 4))
```

* `dup(x, x)` liga `a` e `b` a uma só posição. Cada escrita muda o que o outro lê, 4 em vez de 3.

* O preço da passagem por referência. Um corpo não pode supor que dois parâmetros por referência são independentes.

# §14.5 O que C++ deixa indefinido

:::table +header
*
  * Situação
  * C++17
  * Core C++
*
  * `inc(5)`
  * erro de compilação
  * erro de tipo
*
  * `const int& r = 5`
  * permitida, temporário estendido
  * excluída
*
  * referência devolvida a local morta
  * indefinida
  * impossível, sem resultados por referência
*
  * referência a objeto liberado
  * indefinida
  * `erro`, posição fora de σ
*
  * duas referências a um argumento
  * aliasing, definido
  * aliasing, definido
:::

# Resumo

* Um parâmetro `τ&` é ligado à *posição* do seu argumento, ligação de referência, nada alocado, nada liberado no retorno.

* O argumento precisa denotar uma posição exatamente do tipo do parâmetro, conferido com ⊢ₗ.

* A troca funciona porque os parâmetros *são* os argumentos.

* Dois parâmetros por referência podem fazer *aliasing* de uma posição, como em C++.

* Core C++ não tem resultados por referência nem referências mortas, então os casos indefinidos de C++ não surgem.

Exercícios: veja as [notas de aula](../pt/Aula-14___-Passagem-por-Refer___ncia/).

```lean -show
end Slides14
```
