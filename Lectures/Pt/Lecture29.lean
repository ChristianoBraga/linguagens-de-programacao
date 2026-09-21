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

#doc (Manual) "Aula 29: Quatro Paradigmas, Um Problema" =>

%%%
tag := "aula-29"
%%%

```lean -show
namespace Lecture29
open CoreCpp
open CoreCpp.Logic
```

A última aula põe um problema em quatro paradigmas e os compara pelos critérios que o curso usa desde o início. A comparação é o segundo objetivo do plano de disciplina, e ela vale alguma coisa aqui apenas porque o primeiro objetivo veio antes. Cada um dos quatro programas é lido por regras que o curso escreveu, então a comparação é entre significados e não entre impressões.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-29.pt.html).*

# O Problema

%%%
tag := "problema"
%%%

A soma dos números pares de 1 a n. O problema é pequeno de propósito, porque a comparação deve ser sobre como cada paradigma diz uma coisa e não sobre qual é melhor em uma coisa difícil. Ele tem as três partes de que uma comparação precisa, uma acumulação, um filtro e uma repetição, e cada paradigma exprime as três de outro modo.

A versão imperativa acumula em uma variável e repete com um laço.

```lean (name := caseImp)
def caseImp : String :=
  "int sumEven(int n) {
     int acc = 0;
     for (int i = 1; i <= n; i = i + 1) {
       if (i % 2 == 0) { acc = acc + i; }
     }
     return acc;
   }
   int main() { return sumEven(10); }"

#eval (parseProgram caseImp).map fun p => (fragment .imperative p, run p)
```
```leanOutput caseImp
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

A versão orientada a objetos da {secref}[aula-26] faz do acumulador o estado de um objeto e do filtro um método `virtual`, então um filtro novo é uma classe nova. A versão funcional da {secref}[aula-27] faz do acumulador um parâmetro e do filtro um valor de função, então um filtro novo é um argumento novo. A versão lógica enuncia a relação entre um número e a soma, com uma cláusula por caso do filtro.

```lean (name := caseLogic)
def caseLogic : String :=
  "sum_even(0, 0).
   sum_even(N, S) :-
     N > 0, 0 =:= N mod 2,
     M is N - 1, sum_even(M, T), S is T + N.
   sum_even(N, S) :-
     N > 0, 1 =:= N mod 2,
     M is N - 1, sum_even(M, S).
   ?- sum_even(10, S)."

#eval match Logic.parse caseLogic with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput caseLogic
?- sum_even(10, S).
S = 30
```

Os quatro programas estão no repositório, três em `examples/` e um em `examples/logic/`, e os quatro dão 30.

# A Comparação

%%%
tag := "comparacao-paradigmas"
%%%

A {numref}[tbl-compare] responde, para cada paradigma e sobre esses quatro programas, às quatro perguntas que o curso faz a toda construção desde a {secref}[aula-1].

:::table +header
*
  * Critério
  * Imperativo
  * Orientado a objetos
  * Funcional
  * Lógico
*
  * Como o estado é expresso
  * uma variável, uma posição de σ escrita muitas vezes
  * um campo de um objeto, uma posição que sobrevive à chamada
  * um parâmetro, uma posição escrita uma vez
  * sem estado, uma substituição cresce com a busca
*
  * Como a abstração é expressa
  * a função, chamada pelo nome
  * o método, selecionado pela etiqueta de classe
  * o valor de função, passado como argumento
  * o predicado, selecionado pela unificação com a cabeça
*
  * Como a repetição é expressa
  * o laço, com a regra que recorre à própria conclusão
  * o laço, sobre uma coleção de objetos
  * a chamada recursiva
  * a cláusula recursiva
*
  * O que o sistema de tipos verifica
  * o tipo de toda expressão e de toda atribuição
  * o acima, e visibilidade, despacho e subtipagem
  * o acima, e o tipo de todo valor de função
  * nada, a linguagem não é tipada
*
  * O que a semântica garante
  * disciplina de pilha em σ, nenhuma posição pendente
  * toda posição do monte é alcançada por ponteiro ou por `this`
  * a memória é escrita uma vez, transparência referencial
  * uma resposta é uma prova da consulta a partir das cláusulas
*
  * Onde fica o ponto de extensão
  * o corpo da função
  * a hierarquia de classes
  * a lista de argumentos
  * o conjunto de cláusulas
:::

{tabcap "tbl-compare"}[Os quatro paradigmas sobre o mesmo problema, pelos critérios do curso.]

Três leituras da tabela merecem registro.

*A última linha é a mesma liberdade gasta de quatro modos.* Cada paradigma tem um lugar em que um programa é fácil de estender sem tocar no que está escrito, e é um lugar diferente em cada um. Esse é o conteúdo prático da escolha de um paradigma, e explica por que um programa costuma misturá‑los, como disse a {secref}[aula-1] e como C++ permite.

*A quinta linha é o que o curso acrescentou.* Uma comparação que parasse nas quatro primeiras linhas é a que um livro-texto faz, e é defensável. A quinta só é possível porque cada paradigma foi lido por regras, e é a que diz o que um programa daquele estilo não pode fazer, e não apenas o que ele não costuma fazer.

*A quarta linha tem um caso à parte.* A linguagem lógica da {secref}[aula-28] não verifica nada antes de correr, então um objetivo que nenhuma cláusula casa simplesmente falha, indistinguível de um objetivo falso. Existe linguagem lógica tipada, e a escolha aqui segue Prolog.

# O Que as Sete Unidades Construíram

%%%
tag := "fechamento"
%%%

O curso começou com uma pergunta, o que significa uma construção de uma linguagem de programação, e a respondeu da mesma maneira vinte e nove vezes, com um juízo e uma regra. A {numref}[tbl-units] é o balanço.

:::table +header
*
  * UD
  * O que acrescentou ao núcleo
  * O que acrescentou à semântica
*
  * I
  * a gramática e a sintaxe abstrata
  * os quatro juízos, ρ e σ
*
  * II
  * tipos, classes com campos, ponteiros, vetores
  * Γ ⊢ e : τ, os valores do monte
*
  * III
  * a referência local, os atributos de uma variável
  * escopo como restauração de ρ, tempo de vida como retirada de σ
*
  * IV
  * parâmetros por referência, lambdas, `std::function`
  * o closure, as regras da chamada
*
  * V
  * métodos, construtores, destrutores, herança
  * `this`, despacho, `delete`
*
  * VI
  * sobrecarga, membros operadores, templates
  * resolução em Γ, instanciação por substituição
*
  * VII
  * nada
  * os fragmentos e a resolução SLD
:::

{tabcap "tbl-units"}[O que cada unidade acrescentou a Core C++ e à sua semântica.]

Três coisas valem ser levadas.

*Um só modelo de memória, da primeira regra à última.* ρ leva identificadores a posições e σ leva posições a valores, e essa decisão, tomada na {secref}[aula-3] antes de haver o que guardar, é a razão de a referência da {secref}[aula-10], o closure da {secref}[aula-15] e o objeto da {secref}[aula-18] custarem uma regra cada em vez de uma reescrita de todas.

*Nenhum comportamento indefinido, pago construção a construção.* Em todo lugar em que C++17 nada diz, Core C++ diz `erro` ou rejeita o programa. Os oito resultados `erro` são o preço, e a recompensa é que toda pergunta sobre um programa do núcleo tem resposta que as regras dão.

*As regras correm.* Toda regra do curso é um caso de uma função Lean, toda derivação destas notas foi impressa pelo interpretador e todo exemplo foi comparado com `g++`. É isso que mantém as regras honestas, e é a parte do método que o curso defenderia primeiro.

O que o curso não fez também merece ser nomeado. Ele não provou nada. As propriedades da {secref}[aula-25] à {secref}[aula-27], o progresso da {secref}[aula-3] e a afirmação LL(1) da {secref}[aula-2] são todas verificadas por inspeção, e uma prova em Lean de qualquer uma delas é o passo natural para quem a quiser. A divergência não tem derivação, e a semântica é silenciosa sobre programas que não terminam. E Core C++ é um subconjunto, então as construções de C++ que ele deixa de fora, as da tabela de discrepâncias, foram mostradas em C++ real e nunca modeladas.

# Exercícios

%%%
tag := "exercicios-29"
%%%

{exercise "exr-case-fifth"}[] Acrescente uma quinta coluna à {numref}[tbl-compare] para Python, e preencha as seis linhas com o que o curso disse sobre tipagem dinâmica. Diga que linha Python não compartilha com nenhuma outra coluna.

{exercise "exr-case-extend"}[] Estenda as quatro versões do estudo de caso com um segundo filtro, os múltiplos de três, de modo que o programa some os números que passam em um ou no outro. Diga, para cada versão, quantas linhas mudaram e quantas delas estão em código que já existia.

{exercise "exr-case-mix"}[] Escreva uma versão do estudo de caso que não pertence a fragmento algum, usando um objeto e um lambda juntos, e diga o que ela ganha sobre as duas. Depois diga que afirmação da {secref}[aula-26] e da {secref}[aula-27] ela abandona.

{exercise "exr-case-semantics"}[] Para cada uma das quatro versões, diga o que a semântica do curso garante sobre ela e não garante sobre as outras três, e dê um programa que mostre a diferença.

{exercise "exr-case-invariant"}[] A versão imperativa tem um invariante de laço. Enuncie‑o, e depois enuncie a propriedade correspondente da versão funcional e da versão lógica. Diga qual das três é uma especificação e qual é o próprio programa.

{exercise "exr-case-directions"}[] A versão lógica responde à consulta com o primeiro argumento dado. Diga o que acontece quando o segundo é dado no lugar, explique o resultado pela regra `SLD-Is`, e altere o programa de modo que as duas direções funcionem, ou argumente que não podem.

```lean -show
end Lecture29
```
