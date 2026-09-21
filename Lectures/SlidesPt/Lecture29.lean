/-
Slides da Aula 29. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Quatro Paradigmas, Um Problema" =>

O estudo de caso, a comparação, e o que as sete unidades construíram

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-29___-Quatro-Paradigmas___-Um-Problema/)

```lean -show
namespace Slides29
open CoreCpp
open CoreCpp.Logic
```

# §29.1 O problema

* A soma dos números pares de 1 a n. Pequeno de propósito, porque a comparação é sobre *como cada paradigma diz uma coisa*.

* Três partes, uma *acumulação*, um *filtro* e uma *repetição*, expressas de outro modo por cada um.

```lean (name := caseImp)
def caseImp : String :=
  "int somaPares(int n) {
     int acc = 0;
     for (int i = 1; i <= n; i = i + 1) {
       if (i % 2 == 0) { acc = acc + i; }
     }
     return acc;
   }
   int main() { return somaPares(10); }"

#eval (parseProgram caseImp).map fun p => (fragment .imperative p, run p)
```
```leanOutput caseImp
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

# §29.1 O mesmo problema, quatro modos

::::cols
:::col
{lbl}[Orientado a objetos]

O acumulador é o estado de um objeto, o filtro um método `virtual`. Um filtro novo é uma *classe nova*.
:::
:::col
{lbl}[Funcional]

O acumulador é um parâmetro, o filtro um valor de função. Um filtro novo é um *argumento novo*.
:::
::::

```lean (name := caseLogic)
def caseLogic : String :=
  "soma_pares(0, 0).
   soma_pares(N, S) :-
     N > 0, 0 =:= N mod 2,
     M is N - 1, soma_pares(M, T), S is T + N.
   soma_pares(N, S) :-
     N > 0, 1 =:= N mod 2,
     M is N - 1, soma_pares(M, S).
   ?- soma_pares(10, S)."

#eval match Logic.parse caseLogic with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput caseLogic
?- soma_pares(10, S).
S = 30
```

# §29.2 A comparação

:::table +header
*
  * Critério
  * Imperativo
  * Orientado a objetos
  * Funcional
  * Lógico
*
  * Estado
  * uma variável
  * um campo de um objeto
  * um parâmetro
  * sem estado, uma substituição
*
  * Abstração
  * a função
  * o método, por etiqueta
  * o valor de função
  * o predicado, por unificação
*
  * Repetição
  * o laço
  * o laço sobre objetos
  * a chamada recursiva
  * a cláusula recursiva
*
  * O sistema de tipos verifica
  * toda expressão
  * e visibilidade, despacho, subtipagem
  * e todo valor de função
  * nada
*
  * A semântica garante
  * disciplina de pilha em σ
  * toda posição do monte por ponteiro ou `this`
  * a memória escrita uma vez
  * uma resposta é uma prova
*
  * O ponto de extensão
  * o corpo da função
  * a hierarquia de classes
  * a lista de argumentos
  * o conjunto de cláusulas
:::

# §29.2 Três leituras

* *A última linha é uma liberdade gasta de quatro modos.* Cada paradigma tem um lugar fácil de estender, e é um lugar diferente. É por isso que os programas os misturam.

* *A quinta linha é o que este curso acrescentou.* Uma comparação que para nas quatro primeiras é a de livro-texto. A quinta diz o que um programa daquele estilo *não pode* fazer.

* *A quarta linha tem um caso à parte.* A linguagem lógica não verifica nada, então um objetivo que nenhuma cláusula casa simplesmente falha.

# §29.3 O que as sete unidades construíram

:::table +header
*
  * UD
  * Ao núcleo
  * À semântica
*
  * I
  * gramática e sintaxe abstrata
  * os quatro juízos, ρ e σ
*
  * II
  * tipos, classes com campos, ponteiros, vetores
  * Γ ⊢ e : τ, os valores do monte
*
  * III
  * a referência local
  * escopo como restauração de ρ, tempo de vida como retirada de σ
*
  * IV
  * parâmetros por referência, lambdas
  * o closure, as regras da chamada
*
  * V
  * métodos, construtores, herança
  * `this`, despacho, `delete`
*
  * VI
  * sobrecarga, operadores, templates
  * resolução em Γ, instanciação por substituição
*
  * VII
  * nada
  * os fragmentos e a resolução SLD
:::

# §29.3 Três coisas para levar

* *Um só modelo de memória, da primeira regra à última.* ρ para posições, σ para valores, decidido antes de haver o que guardar. Por isso a referência, o closure e o objeto custam *uma regra cada*.

* *Nenhum comportamento indefinido, pago construção a construção.* Oito resultados `erro` são o preço, e toda pergunta sobre um programa tem resposta.

* *As regras correm.* Toda regra é um caso de uma função Lean, toda derivação foi impressa, todo exemplo comparado com `g++`.

# §29.3 E o que ele não fez

* *Não provou nada.* As propriedades desta unidade, o progresso da Aula 3 e a afirmação LL(1) da Aula 2 são verificados *por inspeção*. Uma prova em Lean de qualquer um deles é o passo natural.

* *A divergência não tem derivação.* A semântica é silenciosa sobre programas que não terminam.

* *Core C++ é um subconjunto.* O que a tabela de discrepâncias deixa de fora foi mostrado em C++ real e nunca modelado.

# Resumo

* Um problema, quatro paradigmas, e a comparação repousa sobre regras e não sobre impressões.

* Cada paradigma põe o *ponto de extensão* em outro lugar, que é o conteúdo prático da escolha.

* A quinta linha da tabela, o que a semântica garante, é o que a leitura por regras tornou possível.

* Sete unidades, um só modelo de memória, nenhum comportamento indefinido e regras que correm.

* O que resta é a prova, e o curso a deixa como o próximo passo.

Exercícios: veja as [notas de aula](../pt/Aula-29___-Quatro-Paradigmas___-Um-Problema/).

```lean -show
end Slides29
```
