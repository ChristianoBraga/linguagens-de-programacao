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

#doc (Manual) "Aula 16: Avaliação de Parâmetros" =>

%%%
tag := "aula-16"
%%%

```lean -show
namespace Lecture16
open CoreCpp
```

Esta aula fecha a UD IV com a pergunta de *quando* um argumento é avaliado. Core C++ e C++ avaliam todo argumento antes de o corpo executar, a disciplina *estrita*. Outras linguagens adiam a avaliação de um argumento até que o corpo precise dele, a disciplina *preguiçosa*, de que a passagem por nome e a passagem por necessidade são as duas formas. A aula escreve as regras da passagem por nome como regras sem contraparte no núcleo, contrasta‑as com as regras de Core C++, mostra como um lambda simula um argumento adiado, e revê todo o fragmento da linguagem implementado até esta unidade.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-16.pt.html).*

# Avaliação Estrita

%%%
tag := "strict"
%%%

A regra `Call` da {secref}[aula-13] avalia todo argumento antes de o corpo começar, nas premissas ρ, σᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ. Que o corpo use ou não o parâmetro não faz diferença. A função `first` abaixo ignora o seu segundo parâmetro, e a chamada avalia `10 / 0` mesmo assim, então o programa termina em `erro`.

```lean (name := first)
def first : String :=
  "int first(int a, int b) { return a; }
   int main() { return first(1, 10 / 0); }"

#eval (parseProgram first).map run
```
```leanOutput first
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

Esse é o significado da *avaliação estrita*, um argumento é avaliado exatamente uma vez, antes da chamada, e os seus efeitos e os seus erros acontecem quer o valor seja usado quer não. C++, Java, Python e Lean seguem essa disciplina para argumentos de função.

Core C++ tem três operadores que não a seguem. A conjunção, a disjunção e o condicional avaliam o seu segundo operando só quando o primeiro não decide o resultado, pelas regras `And-False`, `Or-True` e as duas regras de `?:` da {secref}[aula-8]. Eles são os operadores *não estritos* embutidos na linguagem, e o programa abaixo usa um deles para proteger a divisão.

```lean (name := curto)
def guarded : String :=
  "int main() { int z = 0;
   return (z == 0 || 10 / z > 1) ? 1 : 0; }"

#eval (parseProgram guarded).map run
```
```leanOutput curto
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

# Passagem por Nome

%%%
tag := "by-name"
%%%

A *passagem por nome* é a disciplina de ALGOL 60, em que um argumento não é avaliado na chamada. O parâmetro representa a *expressão* do argumento, e cada uso do parâmetro no corpo avalia a expressão de novo, no ambiente da chamada. Core C++ não tem essa construção, e a regra abaixo é escrita para um parâmetro hipotético `τ name x`, para mostrar o que mudaria.{margin}[P. Naur (ed.), *Revised Report on the Algorithmic Language ALGOL 60*, Communications of the ACM 6(1), 1963, pp. 1 a 17.]

```
f ↦ (τ f (τ₁ name x₁) { c })
ρ_f = [x₁ ↦ thunk(e₁, ρ)]                     o parâmetro é ligado ao argumento não avaliado e ao seu ambiente
ρ_f, σ ⊢ c ⇒ ret v, ρ', σ'
──────────────────────────────────────────── (Call-Name)
ρ, σ ⊢ f(e₁) ⇒ v, σ'

ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────── (Var-Name)     cada leitura de x avalia e de novo
ρ, σ ⊢ x ⇒ v, σ'
```

Duas coisas rompem o modelo de Core C++. O ambiente deixa de levar identificadores só a posições, um parâmetro por nome é ligado a um par de expressão e ambiente, chamado *thunk*. E uma leitura de variável pode ter efeitos e erros, porque avalia uma expressão. Com essa disciplina `first(1, 10 / 0)` devolve 1, já que `b` nunca é lido, e um parâmetro lido duas vezes avalia o seu argumento duas vezes, o que repete qualquer efeito que o argumento tenha.

# Simulando um Argumento Adiado

%%%
tag := "thunks"
%%%

Os lambdas da {secref}[aula-15] permitem a um programa de Core C++ adiar um argumento. Em vez de um valor, quem chama passa uma função sem parâmetros cujo corpo é a expressão do argumento, e a função chamada a chama quando, e tantas vezes quantas, precisa do valor. A função `first` abaixo tem essa forma, e a chamada com `10 / z` devolve 1, porque o closure nunca é chamado.

```lean (name := primeiroPreguicoso)
def firstLazy : String :=
  "int first(int a, std::function<int()> b) { return a; }
   int main() { int z = 0;
   return first(1, [=]() -> int { return 10 / z; }); }"

#eval (parseProgram firstLazy).map run
```
```leanOutput primeiroPreguicoso
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

O closure faz o papel do thunk, e as suas cópias capturadas fazem o papel do ambiente ρ₀ da regra `Var-Name`. A diferença é que o programador escreve o adiamento, com `[=]() -> int { … }` na chamada e `b()` em cada uso, onde ALGOL 60 o fazia para todo parâmetro.

A simulação também mostra a avaliação repetida da passagem por nome. A função `applyTwice` chama o seu argumento duas vezes, e o argumento incrementa um contador alcançado por um ponteiro capturado, então as duas chamadas veem 1 e 2 e a soma é 3. Uma disciplina que avaliasse o argumento uma vez e lembrasse o valor, a *passagem por necessidade*, daria 2.

```lean (name := duasVezesEfeito)
def twiceEffect : String :=
  "class Box { public: int value; };
   int applyTwice(std::function<int()> t) { return t() + t(); }
   int main() { Box* c = new Box(); c->value = 0;
     return applyTwice([=]() -> int {
       c->value = c->value + 1; return c->value; }); }"

#eval (parseProgram twiceEffect).map run
```
```leanOutput duasVezesEfeito
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

# Avaliação Preguiçosa em Haskell

%%%
tag := "lazy"
%%%

Haskell avalia todo argumento por necessidade. Um argumento é avaliado na primeira vez em que o seu valor é exigido e nunca mais, e um argumento cujo valor nunca é exigido nunca é avaliado.{margin}[S. Peyton Jones, *The Implementation of Functional Programming Languages*, Prentice Hall, 1987, capítulo 11.] A função `first` em Haskell devolve o seu primeiro argumento, e a chamada com uma divisão por zero devolve 1.

```
primeiro :: Int -> Int -> Int
primeiro a b = a

main = print (primeiro 1 (div 10 0))
```

O mesmo programa em Core C++ termina em `erro`, como a {secref}[strict] mostrou. A regra que descreve a disciplina de Haskell é a regra `Call-Name` com uma mudança, o thunk é substituído pelo seu valor depois da primeira avaliação, então a segunda leitura do parâmetro encontra um valor e não avalia nada.

```
ρ(x) = thunk(e, ρ₀)    ρ₀, σ ⊢ e ⇒ v, σ'
──────────────────────────────────────────────── (Var-Need)     a primeira leitura atualiza a ligação
ρ, σ ⊢ x ⇒ v, σ'    e a ligação passa a x ↦ v
```

A passagem por necessidade só é equivalente à passagem por nome quando o argumento não tem efeitos, o que é o caso em Haskell, em que expressões não alteram memória alguma. Em uma linguagem com atribuição as duas disciplinas diferem, como `applyTwice` mostrou, e essa é uma razão para as linguagens imperativas manterem a disciplina estrita para argumentos. A {numref}[tbl-disciplines] resume.

:::table +header
*
  * Disciplina
  * Argumento avaliado
  * Efeitos do argumento
  * Linguagem
*
  * estrita, por valor
  * uma vez, antes da chamada
  * uma vez, sempre
  * Core C++, C++, Java, Python, Lean
*
  * por nome
  * a cada leitura do parâmetro
  * repetidos a cada leitura
  * ALGOL 60
*
  * por necessidade
  * na primeira leitura, se houver
  * uma vez, se lido
  * Haskell
*
  * por valor com um closure
  * a cada chamada do closure
  * a cada chamada
  * simulação em Core C++
:::

{tabcap "tbl-disciplines"}[As disciplinas de avaliação de parâmetros.]

# O Fragmento da UD IV

%%%
tag := "fragment-16"
%%%

A UD IV acrescentou a Core C++ as construções da {numref}[tbl-fragment-16], cada uma com as suas regras de tipos e de avaliação e cada uma implementada no interpretador. A especificação do fragmento é o documento `spec-ud4.md` da disciplina, e o [blueprint](https://christianobraga.github.io/corecpp/) mostra cada regra ao lado da função Lean que a implementa.

:::table +header
*
  * Construção
  * Regras
  * Aula
*
  * passagem por valor, `return`
  * `T-Call`, `Call`, `Return`
  * {secref}[aula-13]
*
  * parâmetros por referência `τ& x`
  * `T-Call` com ⊢ₗ, `Call` com ligação de referência
  * {secref}[aula-14]
*
  * tipos `std::function<τ(…)>`, lambdas `[=]`
  * `T-Lambda`, `Lambda`
  * {secref}[aula-15]
*
  * chamadas de valores de função
  * `T-CallFn`, `CallFn`
  * {secref}[aula-15]
*
  * captura por cópia, somente leitura
  * `T-LocVar` com a marca de somente leitura
  * {secref}[aula-15]
:::

{tabcap "tbl-fragment-16"}[As construções da UD IV e as suas regras.]

Duas decisões de projeto do fragmento merecem uma última palavra. Um closure guarda valores, então nenhum closure pode guardar uma posição que saiu da memória, e a linguagem mantém a sua promessa de nenhum comportamento indefinido. E um valor de função é copiado quando atribuído ou passado, exatamente como um `int`, porque um closure é um valor e não um objeto.

```lean (name := functionValue)
def functionValue : String :=
  "int main() {
   std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
   std::function<int(int, int)> h = g; return h(10, 3); }"

#eval (parseProgram functionValue).map run
```
```leanOutput functionValue
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

# Exercícios

%%%
tag := "exercises-16"
%%%

{exercise "exr-strict-effects"}[] Escreva uma chamada cujo argumento tem um efeito e cujo parâmetro nunca é lido, execute, e explique pela regra `Call` por que o efeito acontece mesmo assim.

{exercise "exr-name-twice"}[] Na passagem por nome, o corpo `return x + x;` com o argumento `next(c)` da {secref}[aula-12] avalia a chamada duas vezes. Dê o resultado para um contador que começa em 0 nas passagens por nome, por necessidade e por valor.

{exercise "exr-simulate-if"}[] Escreva uma função `seNao` que recebe um `bool` e dois valores de tipo `std::function<int()>` e devolve o valor de um deles, e explique por que os dois argumentos precisam ser closures para a função se comportar como `?:`.

{exercise "exr-need-rule"}[] A regra `Var-Need` atualiza uma ligação. Diga o que teria de mudar no ambiente ρ de Core C++, que leva identificadores a posições, para que essa regra fosse escrita sem thunks.

{exercise "exr-haskell-list"}[] Em Haskell a expressão `take 3 [1..]` devolve os três primeiros elementos de uma lista infinita. Explique, pela disciplina de passagem por necessidade, por que o programa termina, e por que nenhum programa de Core C++ pode definir tal lista.

{exercise "exr-review"}[] Para cada construção da {numref}[tbl-fragment-16], escreva um programa de no máximo cinco linhas que o verificador de tipos aceita e um que ele rejeita, e nomeie a regra que o rejeita.

```lean -show
end Lecture16
```
