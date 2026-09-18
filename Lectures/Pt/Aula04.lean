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

#doc (Manual) "Aula 4: Processadores de Linguagens" =>

%%%
tag := "aula-4"
%%%

```lean -show
namespace Aula4
open CoreCpp
```

Esta aula trata os programas que processam programas. Ela distingue interpretadores de compiladores, descreve as fases comuns aos dois, apresenta os diagramas em T que descrevem a combinação de processadores, e examina o interpretador de Core C++ como um processador de linguagem completo, com as suas quatro fases e os seus quatro modos de uso. A aula fecha a UD I e prepara a UD II, em que a verificação de tipos ganha as suas regras.

*Esta aula também está disponível como [slides de apresentação](../slides/aula-4.pt.html).*

# Interpretadores e Compiladores

%%%
tag := "interpretadores-compiladores"
%%%

Um *processador de linguagem* é um programa que recebe programas de uma linguagem fonte como entrada. Dois tipos importam aqui.{margin}[D. A. Watt e D. F. Brown, *Programming Language Processors in Java, Compilers and Interpreters*, Prentice Hall, 2000, capítulo 2.] Um *interpretador* da linguagem L recebe um programa em L e a sua entrada e executa o programa diretamente, produzindo a sua saída. Um *compilador* de L para uma linguagem alvo M recebe um programa em L e produz um programa equivalente em M, que outro processador, muitas vezes o próprio hardware, executa depois.

A diferença é de momento, e não de essência. O compilador faz uma vez, antes da execução, o trabalho de análise que o interpretador refaz a cada execução, e por isso o código compilado costuma ser mais rápido. O interpretador, em troca, dispensa a etapa de tradução, começa a executar imediatamente e pode reportar erros nos termos do programa fonte. As duas formas descrevem a mesma semântica, e um programa bem definido produz o mesmo resultado nas duas.

Muitas implementações combinam as duas formas. CPython compila cada módulo Python para um código intermediário, o *bytecode*, e uma máquina virtual interpreta esse código. A máquina virtual Java faz o mesmo com o bytecode produzido por `javac`, e acrescenta um compilador *just in time*, que traduz para código de máquina, durante a execução, os trechos executados com frequência. O `g++` compila C++ para código de máquina, e o processador executa o resultado sem intermediário.

# As Fases de um Processador

%%%
tag := "fases"
%%%

Interpretadores e compiladores compartilham a *análise* do programa fonte e diferem no que fazem depois dela. A {numref}[tbl-fases] lista as fases e o que cada uma produz, com a fase correspondente do interpretador de Core C++.

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
  * `lex`, em `Lexer.lean`
*
  * análise sintática
  * tokens
  * árvore de sintaxe abstrata
  * `parseProgram`, em `Parser.lean`
*
  * análise contextual
  * árvore
  * árvore verificada, com tipos
  * `check`, em `Typing.lean`
*
  * geração de código ou avaliação
  * árvore verificada
  * programa alvo ou resultado
  * `run`, em `Eval.lean`
:::

{tabcap "tbl-fases"}[As fases de um processador de linguagem e as funções do interpretador de Core C++ que as implementam.]

As três fases de análise formam o *front end* do processador, e dependem só da linguagem fonte. A fase final é o *back end*, e depende do alvo. Um compilador para duas máquinas diferentes compartilha o front end e troca o back end, e um interpretador é um processador cujo back end avalia a árvore em vez de traduzi‑la. A *análise contextual*, também chamada análise semântica, verifica as regras que a gramática livre de contexto não expressa, como a declaração prévia de cada identificador e a compatibilidade dos tipos em cada operação. A {secref}[aula-3] mostrou o juízo Γ ⊢ e : τ que a descreve.

# Diagramas em T

%%%
tag := "diagramas-t"
%%%

Os *diagramas em T*, propostos por Bratman,{margin}[H. Bratman, *An alternate form of the "UNCOL diagram"*, Communications of the ACM 4(3), 1961, p. 142.] descrevem processadores e a sua combinação. Um compilador é um T com a linguagem fonte à esquerda, a linguagem alvo à direita e a linguagem em que o compilador está escrito na base. Um interpretador é um retângulo com a linguagem interpretada em cima e a linguagem de implementação embaixo. Um programa é um retângulo com o nome do programa em cima e a sua linguagem embaixo. Uma máquina é um triângulo com a linguagem que ela executa.

O interpretador de Core C++ está escrito em Lean. O compilador de Lean, por sua vez, traduz Lean para C, e o compilador de C da máquina traduz C para código de máquina. O diagrama abaixo mostra como o interpretador chega a rodar.

```
  ┌────────────────┐        ┌───────────────┐        ┌───────────────┐
  │ interpretador  │        │ Lean  →  C    │        │  C  →  x86    │
  │ de Core C++    │        └───┐       ┌───┘        └───┐       ┌───┘
  ├────────────────┤            │ Lean  │                │  x86  │
  │      Lean      │            └───────┘                └───────┘
  └────────────────┘                                        ▲
                                                            │ executa
                                                        ┌───┴───┐
                                                         ╲ x86 ╱
                                                          ╲   ╱
                                                           ╲ ╱
```

O compilador de Lean está escrito em Lean, o que é comum nas linguagens maduras e se chama *auto‑hospedagem*. Para compilar a primeira versão de um compilador auto‑hospedado é preciso um compilador anterior, escrito em outra linguagem ou compilado por uma versão anterior, e o processo se chama *bootstrapping*. O `g++` é compilado pelo próprio `g++`, e Lean 4 é compilado por Lean 4, a partir de um estágio inicial em C gerado pela versão anterior.

# O Interpretador de Core C++ como Processador

%%%
tag := "corecpp-processador"
%%%

O interpretador `corecpp` recebe um arquivo com um programa e um modo de operação, e cada modo para em uma fase diferente. A {numref}[tbl-modos] os descreve.

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

{tabcap "tbl-modos"}[Os quatro modos do interpretador de Core C++.]

O modo `run` é o padrão, e `-` no lugar do arquivo lê a entrada padrão. O código de saída do processo é o valor devolvido por `main` módulo 256, como o sistema operacional faz com um programa compilado, então a linha abaixo se comporta como compilar com `g++` e executar o resultado.

```
echo 'int main() { return 42; }' | bin/corecpp -; echo $?
```

Um resultado `erro` sai com o código 134, o de um processo abortado, e um erro sintático ou de tipo sai com 1. Esses códigos permitem comparar, em um script, o interpretador com o compilador em cada exemplo do repositório.

Dentro do interpretador as fases são funções encadeadas. A função `parseProgram` chama `lex` e o analisador sintático. A função `check` percorre a árvore com o contexto de tipos. A função `run` avalia a árvore com o ambiente e a memória vazios.

```lean (name := checkOk)
def soma : String :=
  "int main() { int x = 1; x = x + 41; return x; }"

#eval (parseProgram soma).map check
```
```leanOutput checkOk
Except.ok (Except.ok ())
```

A análise contextual detecta o uso de um identificador fora do seu escopo, que a gramática não consegue excluir, porque a gramática não sabe quais nomes foram declarados.

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

Ela também verifica a existência de uma função `int main()`, sem a qual o programa não tem ponto de entrada.

```lean (name := checkMain)
def semMain : String := "bool main() { return true; }"

#eval (parseProgram semMain).map check
```
```leanOutput checkMain
Except.ok (Except.error (CoreCpp.TypeError.missingMain))
```

# Verificação Estática e Dinâmica

%%%
tag := "estatica-dinamica"
%%%

Uma propriedade de um programa é verificada *estaticamente* quando o processador a verifica antes da execução, para todas as execuções de uma vez, e *dinamicamente* quando a verifica durante a execução, para a execução em curso. A análise contextual é estática. A verificação de índice fora dos limites de um vetor é dinâmica, porque depende de valores calculados em execução.

As linguagens diferem em quanto verificam de cada forma. Core C++ e C++ verificam os tipos estaticamente, e um programa que soma `int` com `bool` é rejeitado antes de executar. Python verifica os tipos dinamicamente, e o mesmo erro só aparece quando a soma é executada, o que pode acontecer depois de horas de execução ou nunca, se o ramo errado não for alcançado nos testes.

Core C++ e C++ divergem no que fazem com um programa aceito. O programa abaixo, `type_error.cpp` no repositório, é aceito por `g++`, que converte `true` em 1 e devolve 2, e é rejeitado pelo verificador de tipos de Core C++, que não tem conversões implícitas entre `bool` e `int`.

```
int main() {
  bool b = true;
  int x = b + 1;
  return x;
}
```

Essa é a única direção em que os dois discordam. Todo programa que Core C++ aceita, `g++` aceita e executa com o mesmo resultado. Um programa que `g++` aceita pode estar fora do subconjunto, por usar uma construção excluída ou por depender de uma conversão que Core C++ não tem.

Na direção da execução, Core C++ substitui o comportamento indefinido de C++ pelo resultado `erro`. A divisão por zero, o estouro de `int` e o acesso a uma posição liberada são `erro` em Core C++ e indefinidos em C++, em que o compilador pode produzir qualquer resultado. A {numref}[tbl-verificacao] resume.

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
  * exceção, dinâmica
*
  * `2147483647 + 1`
  * `erro`, dinâmico
  * indefinido
  * inteiro de precisão arbitrária
*
  * variável não declarada
  * erro de tipo, estático
  * erro de compilação
  * exceção, dinâmica
:::

{tabcap "tbl-verificacao"}[A mesma situação em três linguagens, com o momento em que cada uma a detecta.]

# Exercícios

%%%
tag := "exercicios-4"
%%%

{exercise "exr-diagrama-t"}[] Desenhe o diagrama em T da execução de um programa Python em CPython, com o compilador para bytecode e a máquina virtual, ambos escritos em C.

{exercise "exr-bootstrapping"}[] Um compilador de L para x86 está escrito em L, e só existe um compilador de L para x86 escrito em C. Desenhe os diagramas em T dos passos até obter o compilador escrito em L rodando em x86, e explique por que o segundo passo produz um compilador mais confiável do que o primeiro.

{exercise "exr-modos"}[] Para cada exemplo do diretório `examples/` do repositório, preveja o código de saída de `bin/corecpp run` e o compare com o de compilar com `g++` e executar. Explique cada diferença pela tabela da {secref}[estatica-dinamica].

{exercise "exr-fases"}[] Classifique cada mensagem abaixo pela fase do interpretador que a produz. "unexpected character '@'", "expected primary expression", "undeclared variable y", "division by zero".

{exercise "exr-estatico-dinamico"}[] Dê um exemplo de propriedade que Core C++ verifica dinamicamente e que uma linguagem poderia verificar estaticamente, e diga que informação o verificador precisaria para isso.

{exercise "exr-aceito-rejeitado"}[] Escreva um programa aceito por `g++` e rejeitado por Core C++ que não use conversão entre `bool` e `int`, e um programa aceito por Core C++ cujo resultado em `g++` você consiga prever pela semântica da {secref}[aula-3].

```lean -show
end Aula4
```
