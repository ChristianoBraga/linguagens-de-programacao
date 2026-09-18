/-
Slides da Aula 4. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Processadores de Linguagens" =>

Interpretadores, compiladores, fases e diagramas em T

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-4___-Processadores-de-Linguagens/)

{cite}[D. A. Watt e D. F. Brown, *Programming Language Processors in Java*, Prentice Hall, 2000, capítulo 2.]

```lean -show
namespace SlidesAula4
open CoreCpp
```

# §4.1 Interpretadores e compiladores

* Um *processador de linguagem* recebe programas como entrada.

* Um *interpretador* de L recebe um programa em L e a sua entrada, e o *executa*.

* Um *compilador* de L para M recebe um programa em L e produz um programa *equivalente* em M.

* A diferença é de *momento*. O compilador analisa uma vez, antes da execução. O interpretador refaz a análise a cada execução e reporta erros nos termos do fonte.

* CPython compila para bytecode e interpreta. A JVM interpreta bytecode e compila *just in time*. O `g++` compila para código de máquina.

# §4.2 As fases

:::table +header
*
  * Fase
  * Entrada
  * Saída
  * Em Core C++
*
  * análise léxica
  * caracteres
  * tokens
  * `lex`
*
  * análise sintática
  * tokens
  * árvore de sintaxe abstrata
  * `parseProgram`
*
  * análise contextual
  * árvore
  * árvore verificada
  * `check`
*
  * geração ou avaliação
  * árvore verificada
  * programa alvo ou resultado
  * `run`
:::

* As três primeiras são o *front end*, dependem só da linguagem fonte. A última é o *back end*, depende do alvo.

# §4.3 Diagramas em T

```tree
  ┌────────────────┐        ┌───────────────┐        ┌───────────────┐
  │ interpretador  │        │ Lean  →  C    │        │  C  →  x86    │
  │ de Core C++    │        └───┐       ┌───┘        └───┐       ┌───┘
  ├────────────────┤            │ Lean  │                │  x86  │
  │      Lean      │            └───────┘                └───────┘
  └────────────────┘                                        ▲
                                                        ┌───┴───┐
                                                         ╲ x86 ╱
                                                          ╲   ╱
                                                           ╲ ╱
```

* Compilador é um T, fonte à esquerda, alvo à direita, linguagem de implementação na base. Interpretador é um retângulo. Máquina é um triângulo.

* Lean é *auto‑hospedado*, compilado por Lean. O primeiro compilador exige *bootstrapping*.

{cite}[H. Bratman, *An alternate form of the "UNCOL diagram"*, Communications of the ACM 4(3), 1961.]

# §4.4 O interpretador de Core C++

:::table +header
*
  * Modo
  * Fases
  * Saída
*
  * `ast`
  * léxica e sintática
  * a árvore de sintaxe abstrata
*
  * `check`
  * até a contextual
  * aceitação ou o erro de tipo
*
  * `run`
  * todas
  * o valor de `main`, também como código de saída
*
  * `trace`
  * todas
  * a árvore de derivação e o valor de `main`
:::

```
echo 'int main() { return 42; }' | bin/corecpp -; echo $?
```

* O código de saída é o valor de `main` módulo 256. `erro` sai com 134, erro sintático ou de tipo com 1.

# §4.4 A análise contextual

```lean (name := checkScope)
def escopo : String :=
  "int main() {
     int x = 1;
     { int y = 2; x = x + y; }
     return y;
   }"

#eval (parseProgram escopo).map check
```
```leanOutput checkScope
Except.ok (Except.error (CoreCpp.TypeError.undeclaredVariable "y"))
```

* A gramática não sabe quais nomes foram declarados. A análise contextual sabe.

* Ela também exige `int main()`, o ponto de entrada do programa.

# §4.5 Verificação estática e dinâmica

* *Estática*, antes da execução, para todas as execuções. *Dinâmica*, durante a execução, para a execução em curso.

* Core C++ e C++ verificam tipos estaticamente. Python, dinamicamente, e o erro pode aparecer depois de horas ou nunca.

:::table +header
*
  * Situação
  * Core C++
  * C++
  * Python
*
  * `1 + true`
  * erro de tipo, estático
  * aceito, vale 2
  * aceito, vale 2
*
  * `10 / 0`
  * `erro`, dinâmico
  * indefinido
  * exceção
*
  * `2147483647 + 1`
  * `erro`, dinâmico
  * indefinido
  * precisão arbitrária
:::

# §4.5 A única direção de discordância

```
int main() {
  bool b = true;
  int x = b + 1;
  return x;
}
```

* `g++` aceita, converte `true` em 1 e devolve 2. Core C++ *rejeita*, sem conversões implícitas entre `bool` e `int`.

* Todo programa que Core C++ aceita, `g++` aceita e executa com o *mesmo resultado*.

* Onde C++ é indefinido, Core C++ dá `erro`.

# Resumo

* *Interpretadores* executam, *compiladores* traduzem, e muitas implementações combinam os dois.

* Quatro *fases*, léxica, sintática, contextual e geração ou avaliação. Front end e back end.

* *Diagramas em T* descrevem processadores e a sua combinação. Auto‑hospedagem exige bootstrapping.

* O interpretador de Core C++ é um processador completo, com os modos `ast`, `check`, `run` e `trace`.

* Verificação *estática* antes da execução, *dinâmica* durante. Core C++ substitui o indefinido por `erro`.

Exercícios: veja as [notas de aula](../pt/Aula-4___-Processadores-de-Linguagens/).

```lean -show
end SlidesAula4
```
