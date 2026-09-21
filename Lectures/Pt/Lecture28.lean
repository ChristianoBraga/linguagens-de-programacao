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

#doc (Manual) "Aula 28: O Paradigma Lógico" =>

%%%
tag := "aula-28"
%%%

```lean -show
namespace Lecture28
open CoreCpp
open CoreCpp.Logic
```

O quarto paradigma não é um fragmento de Core C++. Nada no núcleo corresponde a um programa que é um conjunto de implicações e a uma computação que é a busca de uma prova, então o curso dá ao paradigma uma linguagem própria, pequena o bastante para uma aula. A aula define os seus termos, dá a unificação e o juízo de resolução SLD na notação usada desde a {secref}[aula-3], e mostra por que uma derivação desse juízo é uma prova e não apenas uma computação. Os alunos reencontram aqui a resolução da disciplina de lógica, agora como semântica operacional.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-28.pt.html).*

# Um Programa de Implicações

%%%
tag := "clausulas"
%%%

Um programa da linguagem é um conjunto de *cláusulas de Horn*, cada uma uma implicação com uma só conclusão.

$$`\begin{array}{lcl} t & ::= & X \mid n \mid f(t_1, \ldots, t_k) \\ A & ::= & p(t_1, \ldots, t_k) \\ C & ::= & A \mid A \mathbin{\texttt{:-}} A_1, \ldots, A_m \\ P & ::= & C_1 \ldots C_n \\ G & ::= & A_1, \ldots, A_k \end{array}`

Um *termo* é uma variável, um inteiro ou um functor aplicado a termos, e uma constante é um functor de aridade zero. Um *átomo* é um símbolo de predicado aplicado a termos. Uma *cláusula* `A :- A₁, …, Aₘ` é lida como a implicação, se todos os `Aᵢ` valem então `A` vale, e uma cláusula sem corpo é um *fato*. Uma *consulta* é uma lista de átomos, e perguntá‑la é perguntar se todos valem e com que valores para as suas variáveis.

Um nome de inicial minúscula é functor ou símbolo de predicado, um de inicial maiúscula é variável, `%` abre um comentário e o ponto final encerra uma cláusula. Uma lista é escrita na notação de colchetes, e o functor por trás dela é `.` sobre a constante que o fonte escreve como um par de colchetes vazio.

A concatenação inteira são duas cláusulas. A primeira diz que a lista vazia concatenada com `L` é `L`, a segunda que concatenar uma lista cuja cabeça é `H` dá um resultado cuja cabeça é `H`.

```lean (name := appendQ)
def appendPl : String :=
  "append([], L, L).
   append([H|T], L, [H|R]) :- append(T, L, R).
   ?- append([1, 2], [3, 4], R).
   ?- append(X, Y, [1, 2])."

#eval match Logic.parse appendPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput appendQ
?- append([1, 2], [3, 4], R).
R = [1, 2, 3, 4]
?- append(X, Y, [1, 2]).
X = []; Y = [1, 2]
X = [1]; Y = [2]
X = [1, 2]; Y = []
```

As duas consultas são o ponto do paradigma. As cláusulas foram escritas uma vez, e respondem tanto à pergunta de qual é a concatenação de duas listas dadas quanto à pergunta de que pares de listas concatenam em uma lista dada. Uma função computa em uma direção, uma relação vale em todas, e nada no programa diz qual argumento é a entrada.

# Unificação

%%%
tag := "unificacao"
%%%

O recurso que faz uma relação correr em várias direções é a *unificação*, a operação que torna dois termos iguais ligando variáveis. Uma *substituição* θ é uma função finita de variáveis em termos, e o juízo é θ ⊢ s ≐ t ⇒ θ', lido como, estendendo θ, os termos `s` e `t` unificam com θ'.

$$`\dfrac{x \notin \mathrm{dom}\ \theta \qquad x \text{ não ocorre em } t}{\theta \vdash X \doteq t \Rightarrow \theta[X \mapsto t]}\;\textsf{(U-Var)}`

$$`\dfrac{}{\theta \vdash n \doteq n \Rightarrow \theta}\;\textsf{(U-Num)}`

$$`\dfrac{\theta_0 = \theta \qquad \theta_{i-1} \vdash s_i \doteq t_i \Rightarrow \theta_i}{\theta \vdash f(s_1 \ldots s_k) \doteq f(t_1 \ldots t_k) \Rightarrow \theta_k}\;\textsf{(U-Fn)}`

Nada mais unifica. Dois functores de nomes diferentes ou de aridades diferentes falham, e um número e um termo composto também. Este é o algoritmo de Robinson.{margin}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, Journal of the ACM 12(1), 1965, pp. 23 a 41.]

Uma variável unifica com um termo.

```lean (name := unify1)
#eval unify [] (.var "X") (.fn "f" [.num 1])
```
```leanOutput unify1
some [("X", CoreCpp.Logic.Term.fn "f" [CoreCpp.Logic.Term.num 1])]
```

A unificação é simétrica no sentido de que os dois lados podem trazer variáveis, e uma chamada liga todas.

```lean (name := unify2)
#eval unify [] (.fn "par" [.var "X", .num 2]) (.fn "par" [.num 1, .var "Y"])
```
```leanOutput unify2
some [("Y", CoreCpp.Logic.Term.num 2), ("X", CoreCpp.Logic.Term.num 1)]
```

A condição lateral da regra `U-Var`, que `X` não ocorre em `t`, é a *verificação de ocorrência*, e é ela que mantém a substituição acíclica. Sem ela, unificar `X` com `f(X)` produziria uma ligação cuja resolução nunca termina.

```lean (name := unify3)
#eval unify [] (.var "X") (.fn "f" [.var "X"])
```
```leanOutput unify3
none
```

A maioria dos sistemas Prolog desliga a verificação de ocorrência, porque ela custa tempo em toda ligação e os programas que dela precisam são raros, e aceita em troca uma resposta incorreta. A linguagem deste curso a mantém ligada, já que o curso apresenta o algoritmo como Robinson o escreveu.{fnref}[ocorrencia]

:::footnotes

{fnAnchor "ocorrencia"}[] A norma ISO deixa indefinido o comportamento de uma unificação que criaria um termo cíclico, que é o mesmo recurso que C++ usa nas situações da {secref}[aula-4], e pela mesma razão, o custo da verificação. Um sistema que a omite pode entrar em laço, imprimir um termo cíclico ou produzir uma resposta errada, e a escolha do curso é pagar o custo e manter a regra como está escrita.

:::

# Resolução SLD

%%%
tag := "sld"
%%%

O significado de uma consulta é dado por um só juízo, na notação usada desde a {secref}[aula-3]. O juízo é P, θ ⊢ G ⇒ θ', lido como, sob o programa P e a substituição θ, a lista de objetivos G tem sucesso com a resposta θ'.

$$`\dfrac{}{P, \theta \vdash \varepsilon \Rightarrow \theta}\;\textsf{(SLD-Empty)}`

$$`\dfrac{\begin{array}{c} (H \mathbin{\texttt{:-}} B_1 \ldots B_m) \text{ variante nova de uma cláusula de } P \\ \theta \vdash A \doteq H \Rightarrow \theta_1 \qquad P, \theta_1 \vdash B_1 \ldots B_m\, G \Rightarrow \theta' \end{array}}{P, \theta \vdash A\, G \Rightarrow \theta'}\;\textsf{(SLD-Resolve)}`

Três coisas estão embutidas na segunda regra. O átomo selecionado é o da esquerda, o que está escrito na forma da conclusão. A cláusula é *renomeada* antes do uso, de modo que um uso não compartilhe variável com outro, que é o que permite a um predicado recursivo chamar a si mesmo. E o corpo da cláusula é posto à frente do resto dos objetivos, então a busca vai em profundidade.

O retrocesso não está nas regras, está na busca. A regra diz que *alguma* cláusula de P se aplica, e uma implementação precisa tentá‑las, na ordem em que estão escritas, e tomar a seguinte quando um ramo falha. Vale dizer essa separação em voz alta, porque as regras dão o significado e a busca dá a estratégia, e uma estratégia diferente sobre as mesmas regras é outro Prolog com as mesmas respostas.

A aritmética não é relacional, e três predicados embutidos o dizem.

$$`\dfrac{\mathrm{eval}(\theta, t) = n \qquad \theta \vdash s \doteq n \Rightarrow \theta_1 \qquad P, \theta_1 \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \mathbin{\texttt{is}} t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Is)}`

$$`\dfrac{\mathrm{eval}(\theta, s) = m \qquad \mathrm{eval}(\theta, t) = n \qquad m \bowtie n \qquad P, \theta \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \bowtie t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Compare)}`

A regra `SLD-Is` avalia o seu lado direito e unifica o resultado com o seu lado esquerdo, então `is` corre em uma só direção, ao contrário de todo outro predicado. Um termo com variável não ligada não tem valor aritmético, e o objetivo que pediu um falha. O fatorial da {secref}[aula-1] mostra a recursão e a aritmética.

```lean (name := factQ)
def fatPl : String :=
  "fatorial(0, 1).
   fatorial(N, F) :- N > 0, M is N - 1, fatorial(M, G), F is N * G.
   ?- fatorial(5, F)."

#eval match Logic.parse fatPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput factQ
?- fatorial(5, F).
F = 120
```

A primeira cláusula é o caso base, e a segunda se guarda com `N > 0` para que as duas não se sobreponham. Lendo a segunda como implicação, se `N` é positivo, `M` é `N` menos um, o fatorial de `M` é `G` e `F` é `N` vezes `G`, então o fatorial de `N` é `F`. O programa é a definição, e a busca é o que transforma a definição em resposta.

# Uma Derivação É uma Prova

%%%
tag := "prova"
%%%

Tudo acima é computação. O que faz do paradigma um paradigma *lógico* é que a computação também é uma prova, e a correspondência é exata o bastante para ser enunciada.

Leia cada cláusula `A :- A₁, …, Aₘ` como a implicação universalmente quantificada da conjunção dos corpos para a cabeça. Leia a consulta `G` como a pergunta de se o fecho existencial da conjunção dos seus átomos decorre do programa. Uma derivação de P, θ ⊢ G ⇒ θ' corresponde então a uma refutação da negação daquele existencial, cada passo de `SLD-Resolve` sendo um passo de resolução entre o objetivo corrente e uma cláusula, com a unificação como o unificador mais geral que a regra de resolução pede. A resposta θ' é a testemunha que o existencial pedia.

Esta é a resolução que a disciplina de lógica apresentou,{margin}[Disciplina 09006, Lógica Matemática, IME, unidade de programação em lógica.] e a única novidade aqui é a restrição que a torna eficiente, que as cláusulas são de Horn, que o átomo selecionado é o da esquerda e que a busca é em profundidade. A leitura de Kowalski, de uma cláusula como enunciado e como procedimento ao mesmo tempo, é o que o nome do paradigma registra.{margin}[R. Kowalski, *Predicate Logic as Programming Language*, IFIP Congress, 1974, pp. 569 a 574.]

Dois limites decorrem da estratégia e não das regras. Um programa *recursivo à esquerda*, cuja cláusula chama a si mesma sobre o mesmo objetivo antes de fazer qualquer coisa, tem derivação infinita e nenhuma finita, então a busca não termina. A implementação do curso limita a profundidade da derivação e informa que não há resposta, que é a mesma acomodação que a {secref}[aula-3] fez com `while (true)`, a semântica não tem derivação e a ferramenta precisa parar de algum modo.

```lean (name := leftRec)
#eval match Logic.parse "q(X) :- q(X). ?- q(1)." with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput leftRec
?- q(1).
false
```

A resposta `false` é o relato honesto da busca limitada, e não é o mesmo que dizer que `q(1)` não vale. Um Prolog de verdade entra em laço aqui. A negação, o corte, `assert` e `retract` ficam fora da linguagem do curso, e cada um deles pediria uma regra que o juízo não tem.

# Exercícios

%%%
tag := "exercicios-28"
%%%

{exercise "exr-logic-member"}[] Escreva as duas cláusulas da pertinência a uma lista, e dê as três respostas da consulta que pede os elementos de uma lista de três elementos. Diga de que cláusula vem cada resposta.

{exercise "exr-logic-reverse"}[] Defina a reversão de uma lista com a concatenação, e diga em que direções a sua definição funciona e em quais não termina.

{exercise "exr-logic-derivation"}[] Construa no papel a derivação da consulta sobre o fatorial com argumento 2, com uma aplicação de `SLD-Resolve` por linha, e marque a substituição depois de cada passo.

{exercise "exr-logic-occurs"}[] Dê uma consulta cuja resposta difere com e sem a verificação de ocorrência, e diga o que um sistema que a omite imprimiria.

{exercise "exr-logic-is"}[] Explique por que a consulta que pede um `N` com `5 is N + 1` falha, e reescreva o fatorial de modo que a consulta que pede o `N` cujo fatorial é 120 funcione, ou argumente que ela não pode com as regras dadas.

{exercise "exr-logic-order"}[] Troque de lugar os dois últimos objetivos da cláusula recursiva do fatorial e explique, pela regra `SLD-Is`, o que muda. Depois troque as duas cláusulas de lugar e explique o que muda na busca e não nas respostas.

```lean -show
end Lecture28
```
