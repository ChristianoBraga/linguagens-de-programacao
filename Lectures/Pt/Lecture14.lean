import VersoManual
import Lectures.Meta.Lean
import Lectures.Meta.Hover
import Lectures.Meta.Label
import Lectures.Meta.Footnote
import Lectures.Papers
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true
set_option lectures.language "pt"

#doc (Manual) "Aula 14: Passagem por Referência" =>

%%%
tag := "aula-14"
%%%

```lean -show
namespace Lecture14
open CoreCpp
```

Esta aula acrescenta o segundo mecanismo de passagem de parâmetros de Core C++, a passagem por referência. Um parâmetro `τ& x` é ligado à posição do seu argumento, e não a uma cópia nova, então uma escrita no parâmetro é uma escrita no argumento. A aula escreve a regra da chamada com os dois tipos de parâmetro, mostra a troca clássica, examina o aliasing entre parâmetros, e lista o que C++ deixa indefinido em torno de referências e o que Core C++ exclui por construção.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-14.pt.html).*

# Um Parâmetro Ligado a uma Posição

%%%
tag := "by-reference"
%%%

A {secref}[aula-10] introduziu a referência local `τ& y = e`, um segundo nome para a posição que $`e` denota. Um *parâmetro por referência* é a mesma construção em uma chamada. A declaração `void inc(int& r)` diz que `r` é um nome para a posição do argumento que a chamada fornecer, e o argumento precisa, portanto, denotar uma posição, uma variável, um campo, um ponteiro desreferenciado ou um elemento de vetor. Um literal ou o resultado de uma expressão aritmética não é admitido.

No ambiente da função a ligação de `r` é de referência, no sentido da {secref}[aula-10], e o retorno não a libera. A regra da chamada da {secref}[aula-13] ganha um caso por parâmetro.

```
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
para cada i, da esquerda para a direita, com σ'₀ = σ,
  pᵢ = τᵢ      ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)      por valor, uma posição nova com a cópia
  pᵢ = τᵢ&     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ                               por referência, a posição do argumento
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
─────────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓᵢ | pᵢ por valor}
```

Os dois casos diferem em uma premissa. Um parâmetro por valor avalia o seu argumento com ⇒, para um valor, e aloca. Um parâmetro por referência avalia o seu argumento com ⇒ₗ, para uma posição, e não aloca nada. O ambiente da função liga os dois tipos de parâmetro a posições, então o corpo os trata do mesmo modo, e só o passo final os distingue, as cópias saem da memória e os referentes ficam.

A regra de tipos acrescenta a premissa correspondente. Para um parâmetro por referência o argumento é conferido com o juízo de posição Γ ⊢ₗ, e o seu tipo precisa ser exatamente o tipo do parâmetro, sem a conversão de `nullptr`, porque `nullptr` não denota posição.

```
f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c })
Γ ⊢ eᵢ : τᵢ' com τᵢ' ≈ τᵢ para cada pᵢ = τᵢ    Γ ⊢ₗ eⱼ : τⱼ para cada pⱼ = τⱼ&
──────────────────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

# Troca

%%%
tag := "swap"
%%%

A função `swap` permuta os conteúdos de duas posições. Na passagem por valor ela permutaria duas cópias e deixaria os argumentos intactos. Na passagem por referência os parâmetros são os argumentos, e a permuta é visível em `main`.

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

A árvore mostra o mecanismo. Os argumentos `x` e `y` são avaliados com ⇒ₗ para ℓ0 e ℓ1, e o ambiente de `swap` é \[a ↦ ℓ0, b ↦ ℓ1\], as mesmas posições sob nomes novos. A local `t` recebe uma posição nova ℓ2. As duas atribuições escrevem em ℓ0 e ℓ1, e depois da chamada `main` lê os valores permutados por `x` e `y`. Só ℓ2 sai da memória no retorno, a variável local do corpo, e os referentes ℓ0 e ℓ1 ficam.{fnref}[locals]

```lean (name := trocaTrace)
#eval match parseProgram swap with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput trocaTrace
ρ₀ = []                            σ₀ = {}
ρ₁ = [x ↦ ℓ0]                      σ₁ = {ℓ0 ↦ 1}
ρ₂ = [x ↦ ℓ0, y ↦ ℓ1]              σ₂ = {ℓ0 ↦ 1, ℓ1 ↦ 2}
ρ₃ = [a ↦ ℓ0, b ↦ ℓ1]              σ₃ = {ℓ0 ↦ 1, ℓ1 ↦ 2, ℓ2 ↦ 1}
ρ₄ = [a ↦ ℓ0, b ↦ ℓ1, t ↦ ℓ2]      σ₄ = {ℓ0 ↦ 2, ℓ1 ↦ 2, ℓ2 ↦ 1}
                                   σ₅ = {ℓ0 ↦ 2, ℓ1 ↦ 1, ℓ2 ↦ 1}
                                   σ₆ = {ℓ0 ↦ 2, ℓ1 ↦ 1}

                   𝒟₇                                      𝒟₈                                      𝒟₉                                          𝒟₁₀
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ int y = 2; ⇒ normal, ρ₂, σ₂    ρ₂, σ₂ ⊢ swap(x, y); ⇒ normal, ρ₂, σ₆    ρ₂, σ₆ ⊢ return x * 10 + y; ⇒ ret 21, ρ₂, σ₆
  ───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 21, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₃, σ₂ ⊢ a ⇒ₗ ℓ0, σ₂
  ───────────────────────────── (Var)
  ρ₃, σ₂ ⊢ a ⇒ 1, σ₂
  ──────────────────────────────────── (Decl)
  ρ₃, σ₂ ⊢ int t = a; ⇒ normal, ρ₄, σ₃

𝒟₂
  ──────────────────── (LocVar)
  ρ₄, σ₃ ⊢ b ⇒ₗ ℓ1, σ₃
  ───────────────────────────── (Var)    ──────────────────── (LocVar)
  ρ₄, σ₃ ⊢ b ⇒ 2, σ₃                     ρ₄, σ₃ ⊢ a ⇒ₗ ℓ0, σ₃
  ──────────────────────────────────────────────────────────────────── (Assign)
  ρ₄, σ₃ ⊢ a = b; ⇒ normal, ρ₄, σ₄

𝒟₃
  ──────────────────── (LocVar)
  ρ₄, σ₄ ⊢ t ⇒ₗ ℓ2, σ₄
  ───────────────────────────── (Var)    ──────────────────── (LocVar)
  ρ₄, σ₄ ⊢ t ⇒ 1, σ₄                     ρ₄, σ₄ ⊢ b ⇒ₗ ℓ1, σ₄
  ──────────────────────────────────────────────────────────────────── (Assign)
  ρ₄, σ₄ ⊢ b = t; ⇒ normal, ρ₄, σ₅

𝒟₄
  ──────────────────── (LocVar)    ──────────────────── (LocVar)                     𝒟₁                                    𝒟₂                                  𝒟₃
  ρ₂, σ₂ ⊢ x ⇒ₗ ℓ0, σ₂             ρ₂, σ₂ ⊢ y ⇒ₗ ℓ1, σ₂             ρ₃, σ₂ ⊢ int t = a; ⇒ normal, ρ₄, σ₃    ρ₄, σ₃ ⊢ a = b; ⇒ normal, ρ₄, σ₄    ρ₄, σ₄ ⊢ b = t; ⇒ normal, ρ₄, σ₅
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₂, σ₂ ⊢ swap(x, y) ⇒ void, σ₆

𝒟₅
  ──────────────────── (LocVar)
  ρ₂, σ₆ ⊢ x ⇒ₗ ℓ0, σ₆
  ───────────────────────────── (Var)    ──────────────────── (Lit)
  ρ₂, σ₆ ⊢ x ⇒ 2, σ₆                     ρ₂, σ₆ ⊢ 10 ⇒ 10, σ₆
  ───────────────────────────────────────────────────────────────── (Binary)
  ρ₂, σ₆ ⊢ x * 10 ⇒ 20, σ₆

𝒟₆
  ──────────────────── (LocVar)
  ρ₂, σ₆ ⊢ y ⇒ₗ ℓ1, σ₆
  ───────────────────────────── (Var)
  ρ₂, σ₆ ⊢ y ⇒ 1, σ₆

𝒟₇
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 1 ⇒ 1, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁

𝒟₈
  ────────────────── (Lit)
  ρ₁, σ₁ ⊢ 2 ⇒ 2, σ₁
  ──────────────────────────────────── (Decl)
  ρ₁, σ₁ ⊢ int y = 2; ⇒ normal, ρ₂, σ₂

𝒟₉
                𝒟₄
  ρ₂, σ₂ ⊢ swap(x, y) ⇒ void, σ₆
  ───────────────────────────────────── (ExprStmt)
  ρ₂, σ₂ ⊢ swap(x, y); ⇒ normal, ρ₂, σ₆

𝒟₁₀
             𝒟₅                       𝒟₆
  ρ₂, σ₆ ⊢ x * 10 ⇒ 20, σ₆    ρ₂, σ₆ ⊢ y ⇒ 1, σ₆
  ────────────────────────────────────────────── (Binary)
  ρ₂, σ₆ ⊢ x * 10 + y ⇒ 21, σ₆
  ─────────────────────────────────────────────────────── (Return)
  ρ₂, σ₆ ⊢ return x * 10 + y; ⇒ ret 21, ρ₂, σ₆
```

:::footnotes

{fnAnchor "locals"}[] O retorno de uma chamada libera as cópias dos argumentos por valor e as variáveis locais que o corpo declarou, lidas como as ligações próprias que o corpo acrescentou ao ambiente da função. As ligações de referência, os parâmetros `τ&`, não liberam nada, porque nomeiam posições que existem antes da chamada. A regra é a mesma leitura de ρ' ∖ ρ que o bloco faz na {secref}[aula-10].

:::

# Qualquer Posição É Argumento

%%%
tag := "any-location"
%%%

O argumento de um parâmetro por referência é qualquer expressão que denote uma posição. Um campo de objeto e um elemento de vetor servem, e a função `inc` abaixo os incrementa no lugar.

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

Uma expressão sem posição é rejeitada antes da execução. O literal 5 tem valor e não tem posição, e a chamada `inc(5)` é um erro de tipo.

```lean (name := incLit)
def incrementLiteral : String :=
  "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }"

#eval (parseProgram incrementLiteral).map check
```
```leanOutput incLit
Except.ok (Except.error (CoreCpp.TypeError.refArgument "inc" "r" (CoreCpp.Expr.intLit 5)))
```

O tipo do argumento precisa ser exatamente o tipo do parâmetro. Uma variável `bool` é uma posição, mas não uma posição de tipo `int`.

```lean (name := incBool)
def incrementBool : String :=
  "void inc(int& r) { r = r + 1; }
   int main() { bool b = true; inc(b); return 0; }"

#eval (parseProgram incrementBool).map check
```
```leanOutput incBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument r of inc" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

# Aliasing entre Parâmetros

%%%
tag := "aliasing"
%%%

Dois parâmetros por referência podem receber o mesmo argumento. A função `dup` abaixo se lê como se `a` e `b` fossem distintos, mas a chamada `dup(x, x)` liga ambos à posição de `x`, e cada atribuição muda o que o outro lê. O resultado é 4, e não o 3 que posições distintas dariam.

```lean (name := dup)
def duplicate : String :=
  "void dup(int& a, int& b) { a = a + b; b = b + a; }
   int main() { int x = 1; dup(x, x); return x; }"

#eval (parseProgram duplicate).map run
```
```leanOutput dup
Except.ok (Except.ok (CoreCpp.Val.int 4))
```

O aliasing é o preço da passagem por referência. Uma função não pode supor que dois parâmetros por referência são independentes, e quem lê o seu corpo não sabe, sem olhar cada chamada, se uma escrita em um altera o outro. C++ tem o mesmo comportamento, e as regras de Core C++ o tornam explícito, o ambiente da chamada leva dois nomes a uma posição.

# O que C++ Deixa Indefinido

%%%
tag := "discrepancies"
%%%

As referências em C++ trazem duas fontes de comportamento indefinido que Core C++ exclui por construção. A {numref}[tbl-refs] resume.

:::table +header
*
  * Situação
  * C++17
  * Core C++
*
  * argumento sem posição, `inc(5)`
  * erro de compilação
  * erro de tipo
*
  * `const int& r = 5`, referência a temporário
  * permitida, o temporário vive enquanto `r`
  * excluída, o inicializador denota posição
*
  * referência devolvida a uma local que terminou
  * indefinida
  * impossível, uma referência nunca é resultado
*
  * parâmetro por referência ligado a objeto liberado
  * indefinida
  * `erro`, a posição está fora de σ
*
  * dois parâmetros por referência para um argumento
  * aliasing, definido
  * aliasing, definido
:::

{tabcap "tbl-refs"}[Referências em chamadas em C++17 e em Core C++.]

A terceira linha é a importante. Uma função de C++ pode devolver uma referência a uma das suas locais, e quem chamou lê então uma posição que não existe mais. Core C++ não tem resultados por referência, então a situação não surge, e um parâmetro por referência só nomeia uma posição que existe antes da chamada, em quem chamou ou entre os objetos de σ.

# Exercícios

%%%
tag := "exercises-14"
%%%

{exercise "exr-swap-value"}[] Reescreva `swap` com parâmetros por valor, execute, e explique pelas duas versões da regra `Call` por que o resultado muda.

{exercise "exr-free-locals"}[] A regra `Call` libera as cópias e as locais do corpo. Diga que informação a regra usa para distinguir as locais dos referentes dos parâmetros por referência, e onde o interpretador a guarda.

{exercise "exr-alias-vector"}[] Escreva uma função `void copy(int& from, int& to)` e chame‑a com dois elementos de um vetor, depois com o mesmo elemento duas vezes. Preveja os dois resultados pela regra `Call` e confira com o interpretador.

{exercise "exr-ref-pointer"}[] Um parâmetro `P*& q` é uma referência a uma variável ponteiro. Escreva uma função que atribui `new P()` a esse parâmetro e mostre, com uma árvore, que o ponteiro de quem chamou muda.

{exercise "exr-mechanisms"}[] Classifique cada parâmetro dos programas desta aula pelo seu mecanismo e, para cada chamada, liste as posições que saem da memória no retorno.

```lean -show
end Lecture14
```
