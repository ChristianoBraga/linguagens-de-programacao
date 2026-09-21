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

#doc (Manual) "Aula 13: Funções e Passagem por Valor" =>

%%%
tag := "aula-13"
%%%

```lean -show
namespace Lecture13
open CoreCpp
```

Esta aula abre a UD IV, Abstração. Uma abstração dá nome e parâmetros a um trecho de programa para que ele seja usado muitas vezes com argumentos diferentes. A aula revê os dois tipos de abstração que Core C++ tem desde a UD I, funções e procedimentos, e dá à regra da chamada a sua leitura completa. Uma chamada por valor aloca uma posição nova com uma cópia de cada argumento, executa o corpo em um ambiente que contém só os parâmetros e libera as cópias no retorno. O comando `return` é um resultado de controle que sobe até a chamada que o consome.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-13.pt.html).*

# Abstração

%%%
tag := "abstraction"
%%%

Toda linguagem oferece meios de nomear um trecho de programa e reutilizá‑lo. Watt os chama abstrações{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, capítulo 5.] e os classifica pela frase que abstraem. Uma *abstração de função* nomeia uma expressão, e a sua chamada é uma expressão que produz um valor. Uma *abstração de procedimento* nomeia um comando, e a sua chamada é um comando que altera a memória. Core C++ escreve as duas como funções, com um tipo de resultado para a primeira e `void` para a segunda, e a {numref}[tbl-abstractions] dá a correspondência.

:::table +header
*
  * Abstração
  * Abstrai
  * A chamada é
  * Em Core C++
*
  * função
  * uma expressão
  * uma expressão com valor
  * `int f(…) { … return e; }`
*
  * procedimento
  * um comando
  * um comando, um efeito em σ
  * `void p(…) { … }`, chamada como `p(…);`
:::

{tabcap "tbl-abstractions"}[Os dois tipos de abstração de Core C++.]

Os *parâmetros* de uma abstração são os nomes que o seu corpo usa para os valores que recebe, e os *argumentos* são as expressões que a chamada fornece. A relação entre um argumento e o seu parâmetro é o *mecanismo de passagem de parâmetros*, e o significado de uma chamada depende dele. A UD I fixou um mecanismo, a passagem por valor. Esta aula escreve a sua regra por completo, a {secref}[aula-14] acrescenta a passagem por referência, a {secref}[aula-15] acrescenta abstrações como valores, e a {secref}[aula-16] compara os mecanismos de outras linguagens.

# A Regra da Chamada

%%%
tag := "call-rule"
%%%

Seja $`f` declarada como $`\tau\ f(\tau_1\ x_1, \ldots, \tau_k\ x_k)\ \{c\}`. Uma chamada $`f(e_1, \ldots, e_k)` sob ρ e σ segue quatro passos, e a regra registra cada um.

```
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c }) no programa
ρ, σ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ                    argumentos, da esquerda para a direita
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, vᵢ),  σ'₀ = σₖ                          uma posição nova com a cópia de cada valor
ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                                    o ambiente da função
ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''                                   o corpo executa até um return
────────────────────────────────────────────────────────────── (Call)
ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ {ℓ₁, …, ℓₖ}                      as cópias saem da memória
```

Os argumentos são avaliados primeiro, no ambiente da chamada e da esquerda para a direita, e todo efeito que eles tenham na memória é mantido. Cada valor recebe então uma *posição nova*, e o parâmetro é ligado a ela. Essa é a *passagem por valor*, o parâmetro é uma cópia do argumento, e uma escrita no parâmetro nunca alcança o argumento. O corpo executa sob `ρ_f`, que contém *só os parâmetros*. Core C++ não tem variáveis globais, então nada de quem chama é visível dentro da função chamada, a não ser pelos valores passados. O `return` produz o controle ret v, e a chamada o consome e produz v. Por fim as posições dos parâmetros são retiradas da memória, o fim do seu tempo de vida.

A regra de tipos confere cada argumento com o tipo do seu parâmetro, e o tipo da chamada é o tipo de resultado declarado.

```
f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ' com τᵢ' ≈ τᵢ para cada i
────────────────────────────────────────────────────────────────────── (T-Call)
Γ ⊢ f(e₁, …, eₖ) : τ
```

O programa abaixo chama `square` com um argumento que é ele próprio uma expressão. O argumento é avaliado para 7 antes de o corpo executar, e o parâmetro `n` é uma posição nova que guarda 7.

```lean (name := square)
def square : String :=
  "int square(int n) { return n * n; }
   int main() { int a = 6; return square(a + 1); }"

#eval (parseProgram square).map run
```
```leanOutput square
Except.ok (Except.ok (CoreCpp.Val.int 49))
```

# O Parâmetro É uma Cópia

%%%
tag := "copy"
%%%

A função `twice` abaixo atribui ao seu parâmetro. Na passagem por valor a atribuição escreve na cópia, e a variável `x` de `main` mantém o seu valor. O resultado soma o 42 devolvido ao 21 inalterado.

```lean (name := twice)
def double : String :=
  "int twice(int n) { n = n * 2; return n; }
   int main() { int x = 21; return twice(x) + x; }"

#eval match parseProgram double with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput twice
ρ₀ = []            σ₀ = {}
ρ₁ = [x ↦ ℓ0]      σ₁ = {ℓ0 ↦ 21}
ρ₂ = [n ↦ ℓ1]      σ₂ = {ℓ0 ↦ 21, ℓ1 ↦ 21}
                   σ₃ = {ℓ0 ↦ 21, ℓ1 ↦ 42}

                   𝒟₇                                            𝒟₈
  ρ₀, σ₀ ⊢ int x = 21; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ return twice(x) + x; ⇒ ret 63, ρ₁, σ₁
  ─────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 63, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₂, σ₂ ⊢ n ⇒ₗ ℓ1, σ₂
  ───────────────────────────── (Var)    ────────────────── (Lit)
  ρ₂, σ₂ ⊢ n ⇒ 21, σ₂                    ρ₂, σ₂ ⊢ 2 ⇒ 2, σ₂
  ─────────────────────────────────────────────────────────────── (Binary)
  ρ₂, σ₂ ⊢ n * 2 ⇒ 42, σ₂

𝒟₂
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)
  ρ₁, σ₁ ⊢ x ⇒ 21, σ₁

𝒟₃
            𝒟₁               ──────────────────── (LocVar)
  ρ₂, σ₂ ⊢ n * 2 ⇒ 42, σ₂    ρ₂, σ₂ ⊢ n ⇒ₗ ℓ1, σ₂
  ──────────────────────────────────────────────────────── (Assign)
  ρ₂, σ₂ ⊢ n = n * 2; ⇒ normal, ρ₂, σ₃

𝒟₄
  ──────────────────── (LocVar)
  ρ₂, σ₃ ⊢ n ⇒ₗ ℓ1, σ₃
  ───────────────────────────── (Var)
  ρ₂, σ₃ ⊢ n ⇒ 42, σ₃
  ─────────────────────────────────── (Return)
  ρ₂, σ₃ ⊢ return n; ⇒ ret 42, ρ₂, σ₃

𝒟₅
          𝒟₂                              𝒟₃                                     𝒟₄
  ρ₁, σ₁ ⊢ x ⇒ 21, σ₁    ρ₂, σ₂ ⊢ n = n * 2; ⇒ normal, ρ₂, σ₃    ρ₂, σ₃ ⊢ return n; ⇒ ret 42, ρ₂, σ₃
  ────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₁, σ₁ ⊢ twice(x) ⇒ 42, σ₁

𝒟₆
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)
  ρ₁, σ₁ ⊢ x ⇒ 21, σ₁

𝒟₇
  ──────────────────── (Lit)
  ρ₀, σ₀ ⊢ 21 ⇒ 21, σ₀
  ───────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 21; ⇒ normal, ρ₁, σ₁

𝒟₈
              𝒟₅                        𝒟₆
  ρ₁, σ₁ ⊢ twice(x) ⇒ 42, σ₁    ρ₁, σ₁ ⊢ x ⇒ 21, σ₁
  ───────────────────────────────────────────────── (Binary)
  ρ₁, σ₁ ⊢ twice(x) + x ⇒ 63, σ₁
  ────────────────────────────────────────────────────────── (Return)
  ρ₁, σ₁ ⊢ return twice(x) + x; ⇒ ret 63, ρ₁, σ₁
```

Três detalhes da árvore merecem atenção. O argumento `x` é lido no ambiente de `main`, \[x ↦ ℓ0\], antes de o corpo começar. O corpo executa sob \[n ↦ ℓ1\], um ambiente com uma só ligação, para a posição nova ℓ1 que guarda a cópia 21. Depois da chamada a memória volta a \{ℓ0 ↦ 21\}, a cópia em ℓ1 saiu dela, e `x` continua guardando 21.

# O Return como Controle

%%%
tag := "return"
%%%

O comando `return e` não salta. Ele avalia $`e` e produz o controle ret v, e as regras de sequência, bloco e laço propagam esse controle para cima sem executar o que segue, até que a regra da chamada o consuma. A {secref}[aula-11] deu essas regras, `Seq-Ret`, `While-Ret` e as regras de `if` e de bloco que deixam passar qualquer controle. A chamada é a única regra que transforma ret v de volta em um valor.

Uma função cujo corpo termina com o controle normal não retornou. Para uma função `void` esse é o fim comum de um procedimento, e a chamada produz o valor void. Para uma função com tipo de resultado é um `erro`, porque não há valor a produzir.

```lean (name := semRetorno)
def noReturn : String :=
  "int f(int n) { if (n > 0) { return 1; } }
   int main() { return f(0); }"

#eval (parseProgram noReturn).map run
```
```leanOutput semRetorno
Except.ok (Except.error (CoreCpp.Error.missingReturn "f"))
```

O verificador de tipos não detecta esse caso, porque precisaria saber quais caminhos do corpo alcançam um `return`, uma análise de fluxo fora do alcance da disciplina. C++ deixa o mesmo programa indefinido, e Core C++ lhe dá o resultado `erro`.{fnref}[flow]

Um procedimento é chamado como statement, e o seu valor void é descartado pela regra `ExprStmt`.

```lean (name := noop)
def procedure : String :=
  "void noop() { int x = 1; }
   int main() { noop(); return 3; }"

#eval (parseProgram procedure).map run
```
```leanOutput noop
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

:::footnotes

{fnAnchor "flow"}[] Um compilador que queira rejeitar o programa em tempo de compilação calcula, para cada função, se todo caminho da entrada ao fim do corpo passa por um `return`. Java exige essa análise e rejeita um método que possa chegar ao fim sem devolver um valor. C++ só avisa. Core C++ escolhe a resposta dinâmica, o resultado `erro`, e deixa a análise como exercício da UD VI.

:::

# Verificação Estática das Chamadas

%%%
tag := "typing-calls"
%%%

A regra `T-Call` fixa o que é verificado antes da execução. A função precisa existir, o número de argumentos precisa coincidir, e cada argumento precisa ter o tipo do seu parâmetro, com a conversão de `nullptr` para tipo ponteiro como única tolerância. Uma chamada de `f` com um `bool` onde se espera um `int` é rejeitada.

```lean (name := callType)
def wrongArgument : String :=
  "int f(int n) { return n; } int main() { return f(true); }"

#eval (parseProgram wrongArgument).map check
```
```leanOutput callType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "argument n of f" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

Dentro do corpo, os parâmetros são as únicas variáveis do contexto inicial, \[x₁ ↦ τ₁, …, xₖ ↦ τₖ\], e a expressão do `return` é conferida com o tipo de resultado declarado. A regra `T-Fun` da {secref}[aula-4] registra as duas condições.

# Exercícios

%%%
tag := "exercises-13"
%%%

{exercise "exr-trace-two-params"}[] Desenhe a derivação de `int sum(int a, int b) { return a + b; } int main() { return sum(2, 3); }` até o corpo de `sum`, mostrando as duas posições novas e o ambiente da chamada, e compare com a árvore do interpretador.

{exercise "exr-copy-pointer"}[] Um parâmetro de tipo ponteiro também é uma cópia. Escreva uma função `void zero(P* p)` que põe `p->a` em 0 e uma função que atribui `nullptr` ao seu parâmetro ponteiro, e explique, pela regra `Call`, por que a primeira tem efeito visível em `main` e a segunda não.

{exercise "exr-missing-return"}[] Escreva uma função com dois comandos `if` cujos caminhos terminam todos em um `return` e uma em que um caminho não termina, execute as duas com o interpretador, e explique por que o verificador de tipos aceita ambas.

{exercise "exr-recursion"}[] A regra da chamada aloca posições novas a cada chamada. Trace `int f(int n) { if (n == 0) { return 0; } return n + f(n - 1); }` com `f(2)` e conte as posições que existem quando a chamada mais interna retorna.

{exercise "exr-argument-effects"}[] Escreva uma chamada cujos argumentos tenham efeitos na memória, por exemplo por uma função que incrementa um contador alcançado por ponteiro, e explique pela regra `Call` em que memória o corpo começa a executar.

```lean -show
end Lecture13
```
