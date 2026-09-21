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

#doc (Manual) "Aula 5: Valores e Tipos" =>

%%%
tag := "aula-5"
%%%

```lean -show
namespace Lecture5
open CoreCpp
```

Esta aula abre a UD II, sobre tipos. Ela define valores e tipos, apresenta o juízo de tipagem Γ ⊢ e : τ e o contexto Γ, escreve as regras de tipos das expressões que Core C++ já tem, e diz o que um sistema de tipos compra, quais erros ele rejeita antes da execução e quais deixa para o tempo de execução. O fio da unidade é o significado de cada construção, e um tipo é a primeira parte desse significado, o conjunto de valores que a construção pode produzir.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-5.pt.html).*

# Valores e Tipos

%%%
tag := "valores-tipos"
%%%

Um *valor* é um dado que um programa computa, armazena, passa a uma função ou devolve de uma. Em Core C++ os valores da UD I são os inteiros de 32 bits e os dois booleanos, e esta unidade acrescenta ponteiros e os objetos que eles alcançam. Um *tipo* é um conjunto de valores com as operações que se aplicam a eles. O tipo `int` é o conjunto dos inteiros entre $`-2^{31}` e $`2^{31}-1` com os operadores aritméticos e relacionais, e o tipo `bool` é o conjunto dos dois valores de verdade com a negação, a conjunção e a disjunção.

Os tipos classificam os valores, e a classificação serve a dois fins. Ela diz ao processador quanta memória um valor ocupa e como os seus bits se leem, e diz ao programador quais operações fazem sentido sobre um valor. O segundo fim é o que esta unidade desenvolve. Uma operação aplicada a um valor fora do seu tipo não tem significado, e uma linguagem decide o que fazer com esse programa, rejeitá‑lo antes da execução, interrompê‑lo durante a execução, ou deixar a máquina fazer o que os bits disserem.

Watt divide os tipos em *primitivos*, cujos valores são atômicos, e *compostos*, cujos valores se constroem de outros valores.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, capítulo 2.] Os tipos primitivos de Core C++ são `int` e `bool`. Os compostos são as classes e os vetores desta unidade, e os *recursivos* são as classes cujos campos apontam para objetos da mesma classe, como os nós de uma lista. A {numref}[tbl-tipos] resume os tipos da unidade e onde aparecem.

:::table +header
*
  * Espécie
  * Tipos
  * Valores
  * Aula
*
  * primitivo
  * `int`, `bool`
  * inteiros de 32 bits, `true` e `false`
  * esta
*
  * composto
  * `class C` com campos
  * registros de posições, alcançados por `C*`
  * {secref}[aula-6]
*
  * recursivo
  * `class Node` com um campo `Node*`
  * cadeias finitas de registros
  * {secref}[aula-7]
*
  * composto
  * `std::vector<int>`
  * sequências de posições, alcançadas por ponteiro
  * {secref}[aula-7]
:::

{tabcap "tbl-tipos"}[Os tipos da UD II.]

# O Juízo de Tipagem

%%%
tag := "juizo-tipagem"
%%%

O *juízo de tipagem* Γ ⊢ e : τ afirma que a expressão e tem tipo τ no *contexto de tipos* Γ, uma função finita de identificadores em tipos. O contexto faz, para os tipos, o papel que o ambiente ρ faz para as posições. Quando a declaração `int x = 1` é verificada, x entra em Γ com tipo `int`, e cada uso posterior de x lê esse tipo de Γ. O contexto de tipos é a contraparte estática do ambiente, e nunca menciona a memória, porque os tipos se decidem antes de existir qualquer valor.

As regras do juízo têm a mesma forma das regras de avaliação da UD I. Um literal tem o seu tipo, uma variável tem o tipo que Γ lhe dá, e um operador tem uma regra que fixa os tipos dos operandos e o tipo do resultado.

```
─────────────── (T-Lit)      ─────────────── (T-BoolLit)      Γ(x) = τ
Γ ⊢ n : int                  Γ ⊢ b : bool                     ─────────── (T-Var)
                                                              Γ ⊢ x : τ

Γ ⊢ e₁ : int    Γ ⊢ e₂ : int                Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)      ──────────────────────────── (T-Rel)
Γ ⊢ e₁ ⊕ e₂ : int                           Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : bool              Γ ⊢ e : bool             Γ ⊢ e : int
────────────────────────────── (T-Logic)    ────────────── (T-Not)   ────────────── (T-Neg)
Γ ⊢ e₁ ⊙ e₂ : bool                          Γ ⊢ !e : bool            Γ ⊢ -e : int
```

Os operadores aritméticos, ⊕, são `+`, `-`, `*`, `/` e `%`, os relacionais, ⋈, são `<`, `<=`, `>` e `>=`, e os lógicos, ⊙, são `&&` e `||`. A igualdade tem regra própria, porque compara valores de qualquer tipo com valores, `int` com `int`, `bool` com `bool` e, a partir da {secref}[aula-7], ponteiros com ponteiros.

```
Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    τ₁ ≈ τ₂    τ₁, τ₂ têm valores
───────────────────────────────────────────────────────── (T-Eq, ⋈ ∈ {==, !=})
Γ ⊢ e₁ ⋈ e₂ : bool

Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ tem valores
──────────────────────────────────────────────────────── (T-Cond)
Γ ⊢ e₁ ? e₂ : e₃ : τ
```

A relação τ₁ ≈ τ₂ é a igualdade de tipos até os ponteiros chegarem, quando passa a aceitar também `nullptr` diante de um ponteiro. A condição "τ tem valores" exclui `void`, o tipo de uma chamada a função que nada devolve, e, a partir da {secref}[aula-6], os tipos objeto, cujos valores vivem na memória e nunca viajam.

Uma *derivação* de um juízo de tipagem é uma árvore de aplicações de regras, como na avaliação. A derivação abaixo tipa `x + 1 < 10` no contexto Γ = \[x ↦ int\].

```
  Γ(x) = int
  ────────────── (T-Var)   ────────────── (T-Lit)
  Γ ⊢ x : int              Γ ⊢ 1 : int
  ─────────────────────────────────────── (T-Arith)   ─────────────── (T-Lit)
  Γ ⊢ x + 1 : int                                     Γ ⊢ 10 : int
  ──────────────────────────────────────────────────────────────────── (T-Rel)
  Γ ⊢ x + 1 < 10 : bool
```

# Comandos e o Contexto

%%%
tag := "comandos-contexto"
%%%

Comandos não têm tipo, mas alteram o contexto. O juízo Γ ⊢ c ⊣ Γ' afirma que o comando c está bem tipado em Γ e produz o contexto Γ' para os comandos que o seguem. Uma declaração estende o contexto, uma sequência o encadeia, e um bloco descarta a extensão, exatamente como o ambiente se comporta nas regras de avaliação da UD I.

```
Γ ⊢ e : τ'    τ' ≈ τ    τ tem valores          Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ
─────────────────────────────────── (T-Decl)   ───────────────────────────────── (T-Assign)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                         Γ ⊢ e₁ = e₂ ⊣ Γ

Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂                     Γ ⊢ c₁ … cₙ ⊣ Γ'
────────────────────────── (T-Seq)             ──────────────────── (T-Block)
Γ ⊢ c cs ⊣ Γ₂                                  Γ ⊢ { c₁ … cₙ } ⊣ Γ
```

O verificador de tipos de Core C++ implementa essas regras, uma função por juízo, e rejeita um programa na primeira regra que falha. Uma declaração cujo inicializador tem o tipo errado é o caso mais simples.

```lean (name := declMismatch)
#eval (parseProgram "int main() { int x = true; return x; }").map check
```
```leanOutput declMismatch
Except.ok (Except.error (CoreCpp.TypeError.mismatch "initialiser of x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

Um operador aplicado ao tipo errado falha na sua própria regra, e a mensagem nomeia o operador e o tipo que ele recebeu.

```lean (name := arithBool)
#eval (parseProgram "int main() { return (1 < 2) + 1; }").map check
```
```leanOutput arithBool
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

Uma condição que não é booleana falha em `T-Cond`, mesmo onde C++ converteria o inteiro em um valor de verdade. Core C++ não tem essa conversão.

```lean (name := condInt)
#eval (parseProgram "int main() { return 7 / 2 ? 1 : 0; }").map check
```
```leanOutput condInt
Except.ok (Except.error (CoreCpp.TypeError.mismatch "condition" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

Um programa que tipa passa pelo verificador sem mensagem, e a declaração com `auto` toma o tipo do seu inicializador.

```lean (name := autoBool)
#eval (parseProgram "int main() { auto y = 3 > 2; return y ? 1 : 0; }").map run
```
```leanOutput autoBool
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

# O que um Sistema de Tipos Compra

%%%
tag := "sistema-tipos"
%%%

Um *sistema de tipos* é o conjunto das regras de tipos de uma linguagem com a garantia que elas dão. A garantia de Core C++ é a enunciada na {secref}[aula-3]. Toda derivação de um programa bem tipado termina em um valor ou em `erro`, e nunca fica presa em uma construção sem regra. Um programa que soma um `int` a um `bool` não tem regra de avaliação para essa soma, e o sistema de tipos o rejeita antes de o avaliador o encontrar. Um programa que divide por zero tem regra, a que produz `erro`, e o sistema de tipos o deixa passar, porque o divisor é um valor que o verificador não conhece.

A distinção é a que separa verificação *estática* e *dinâmica* na {secref}[aula-4]. O sistema de tipos verifica, antes da execução e para todas as execuções de uma vez, as propriedades que dependem só dos tipos. Tudo o que depende de valores é verificado durante a execução, pelas regras que produzem `erro`. Core C++ move o máximo que pode para o lado estático, mas a fronteira é fixada pelo que o verificador pode saber. A {numref}[tbl-estatico-dinamico] lista as situações desta unidade de cada lado.

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
  * condição de `if` que é `int`
  * estaticamente
  * `T-If`
*
  * variável usada fora do escopo
  * estaticamente
  * `T-Var`, Γ não tem a entrada
*
  * campo que a classe não tem
  * estaticamente
  * `T-Arrow`, na {secref}[aula-6]
*
  * divisão por zero
  * dinamicamente
  * `DivZero`
*
  * estouro de `int`
  * dinamicamente
  * `int32`
*
  * desreferência de `nullptr`
  * dinamicamente
  * `LocDeref`, na {secref}[aula-7]
*
  * índice fora do vetor
  * dinamicamente
  * `LocIndex`, na {secref}[aula-7]
:::

{tabcap "tbl-estatico-dinamico"}[O que o sistema de tipos de Core C++ verifica antes da execução e o que as regras de avaliação verificam durante ela.]

As linguagens diferem em onde põem a fronteira. Python não tem verificação estática, então toda situação da tabela é encontrada durante a execução, se o programa a alcançar. C++ verifica tipos estaticamente, mas aceita conversões que Core C++ rejeita, como a condição inteira acima, e deixa as situações dinâmicas indefinidas em vez de interromper o programa. Lean, a linguagem do interpretador, tem um sistema de tipos rico o bastante para expressar, no tipo de uma função, propriedades que Core C++ só verifica em execução, e a UD VI volta a esse ponto.{fnref}[corretude]

:::footnotes

{fnAnchor "corretude"}[] A garantia de que programas bem tipados nunca ficam presos chama‑se *corretude* do sistema de tipos, ou segurança de tipos, e Pierce a apresenta para uma linguagem pequena como o par de teoremas progresso e preservação.{margin}[B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, capítulo 8.] Para Core C++ a disciplina enuncia a propriedade, a verifica por inspeção do conjunto de regras, e não a prova em Lean.

:::

# Exercícios

%%%
tag := "exercicios-5"
%%%

{exercise "exr-derivacao-tipos"}[] Construa a derivação de tipagem de `(a && b) ? n : n + 1` no contexto Γ = \[a ↦ bool, b ↦ bool, n ↦ int\], nomeando a regra de cada passo.

{exercise "exr-contexto-bloco"}[] Escreva a sequência de contextos Γ₀, Γ₁, … produzida por `int x = 1; { bool b = x < 2; x = b ? 2 : 3; } x = x + 1;`, e diga qual contexto verifica a última atribuição.

{exercise "exr-estatico-ou-dinamico"}[] Para cada situação, diga se Core C++ a detecta estática ou dinamicamente, e nomeie a regra. Um `return` com `bool` em função `int`. Um `while` cuja condição é `x` com `x` do tipo `int`. Um resto por uma variável que vale zero. Uma chamada com dois argumentos a uma função de um parâmetro.

{exercise "exr-cpp-aceita"}[] Escreva três programas que o `g++` aceita e o verificador de tipos de Core C++ rejeita, cada um por uma regra diferente, e preveja o valor que o `g++` computa para cada um.

{exercise "exr-tipo-condicional"}[] A regra `T-Cond` exige que os dois ramos tenham o mesmo tipo. Dê um programa em que os ramos têm tipos diferentes, diga que valor C++ computaria para ele, e explique por que Core C++ prefere a rejeição.

```lean -show
end Lecture5
```
