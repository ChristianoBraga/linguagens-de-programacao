/-
Slides da Aula 28. Cada seção de nível superior é um slide. As regras são
texto preformatado em blocos `tree`.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "O Paradigma Lógico" =>

Cláusulas de Horn, unificação e resolução SLD como semântica operacional

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-28___-O-Paradigma-L___gico/)

{cite}[J. A. Robinson, *A Machine-Oriented Logic Based on the Resolution Principle*, JACM 12(1), 1965.]

```lean -show
namespace Slides28
open CoreCpp
open CoreCpp.Logic
```

# §28.1 Um programa de implicações

* Não é um fragmento de Core C++. Nada no núcleo é um programa de *implicações* e uma computação que é *busca de prova*.

```tree
t ::= X | n | f(t₁, …, tₖ)        termo
A ::= p(t₁, …, tₖ)                átomo
C ::= A | A :- A₁, …, Aₘ          cláusula de Horn, fato ou regra
P ::= C₁ … Cₙ                     programa
G ::= A₁, …, Aₖ                   consulta
```

* Inicial minúscula é functor ou predicado, maiúscula é *variável*.

* Uma cláusula é lida como, se todos os corpos valem então a cabeça vale.

# §28.1 Uma definição, duas perguntas

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

* Uma *função* computa em uma direção. Uma *relação* vale em todas, e nada diz qual argumento é a entrada.

# §28.2 Unificação

```tree
x ∉ dom θ    x não ocorre em t
────────────────────────────── (U-Var)
θ ⊢ X ≐ t ⇒ θ[X ↦ t]

──────────────── (U-Num)
θ ⊢ n ≐ n ⇒ θ

θ₀ = θ    θᵢ₋₁ ⊢ sᵢ ≐ tᵢ ⇒ θᵢ
─────────────────────────────────── (U-Fn)
θ ⊢ f(s₁ … sₖ) ≐ f(t₁ … tₖ) ⇒ θₖ
```

* O algoritmo de Robinson. É ele que faz uma relação correr em várias direções, porque liga as variáveis da consulta *e* da cláusula de uma vez.

# §28.2 A verificação de ocorrência

```lean (name := unify3)
#eval unify [] (.var "X") (.fn "f" [.var "X"])
```
```leanOutput unify3
none
```

* A condição lateral de `U-Var` mantém a substituição *acíclica*.

* A maioria dos sistemas Prolog a desliga, paga menos e aceita uma resposta incorreta. Este curso a mantém.

# §28.3 Resolução SLD

```tree
──────────────── (SLD-Empty)
P, θ ⊢ ε ⇒ θ

(H :- B₁ … Bₘ) variante nova de uma cláusula de P
θ ⊢ A ≐ H ⇒ θ₁    P, θ₁ ⊢ B₁ … Bₘ G ⇒ θ'
───────────────────────────────────────────────── (SLD-Resolve)
P, θ ⊢ A G ⇒ θ'
```

* O átomo *da esquerda* é selecionado, o que está escrito na forma da conclusão.

* A cláusula é *renomeada*, que é o que faz a recursão funcionar.

* *O retrocesso não está nas regras.* As regras dão o significado, a busca dá a estratégia.

# §28.3 A aritmética não é relacional

```tree
eval(θ, t) = n    θ ⊢ s ≐ n ⇒ θ₁    P, θ₁ ⊢ G ⇒ θ'
─────────────────────────────────────────────────── (SLD-Is)
P, θ ⊢ (s is t) G ⇒ θ'
```

```lean (name := factQ)
def fatPl : String :=
  "factorial(0, 1).
   factorial(N, F) :- N > 0, M is N - 1, factorial(M, G), F is N * G.
   ?- factorial(5, F)."

#eval match Logic.parse fatPl with
  | .ok (cs, qs) =>
    let out := qs.map fun q =>
      Logic.answersToString q (Logic.query cs q)
    IO.println ("\n".intercalate out)
  | .error e => IO.println e
```
```leanOutput factQ
?- factorial(5, F).
F = 120
```

# §28.4 Uma derivação é uma prova

* Leia uma cláusula como implicação universalmente quantificada, e uma consulta como a pergunta de se um existencial decorre do programa.

* Uma derivação é então uma *refutação* da negação daquele existencial, cada passo um passo de resolução, com a unificação dando o unificador mais geral.

* A resposta é a *testemunha*. Esta é a resolução da disciplina de lógica, restrita a cláusulas de Horn, seleção à esquerda e busca em profundidade.

* A leitura de Kowalski, uma cláusula é *enunciado* e *procedimento* ao mesmo tempo.

# §28.4 O que a estratégia custa

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

* Um programa *recursivo à esquerda* tem derivação infinita e nenhuma finita. Um Prolog de verdade entra em laço.

* A implementação limita a profundidade, a mesma acomodação que o curso fez com `while (true)`.

* `false` é o relato de uma busca limitada, *não* a afirmação de que o objetivo é falso.

# Resumo

* Um programa é um conjunto de *cláusulas de Horn*, uma consulta é uma lista de átomos, e nada diz qual argumento é a entrada.

* A *unificação* com verificação de ocorrência é o que faz uma relação correr em várias direções.

* A *resolução SLD* é um só juízo, seleção à esquerda, e a busca fornece o retrocesso.

* Uma derivação *é uma prova*, que é o conteúdo do nome do paradigma.

* Fora do escopo. Negação, corte, `assert` e `retract`, e a divergência da recursão à esquerda.

Exercícios: veja as [notas de aula](../pt/Aula-28___-O-Paradigma-L___gico/).

```lean -show
end Slides28
```
