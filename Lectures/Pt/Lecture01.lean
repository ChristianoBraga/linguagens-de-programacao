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

#doc (Manual) "Aula 1: Linguagens e Paradigmas" =>

%%%
tag := "aula-1"
%%%

```lean -show
namespace Lecture1
open CoreCpp
```

Esta aula apresenta o objeto da disciplina, o significado das construções das linguagens de programação, e o seu método, em que cada construção é estudada como parte de uma linguagem núcleo chamada Core C++, com regras de tipos e de avaliação escritas em semântica natural e codificadas em Lean. A aula organiza as construções pelos conceitos de Watt{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990.] e termina com um mesmo programa em quatro paradigmas.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-1.pt.html).*

# Por que Estudar Linguagens de Programação?

%%%
tag := "por-que"
%%%

Um engenheiro de computação programa em várias linguagens ao longo da carreira e escolhe, ou herda, a linguagem de cada projeto. Cada linguagem fixa um conjunto de decisões sobre valores, tipos, memória, controle e abstração, e essas decisões determinam o que é fácil de expressar, o que o compilador verifica e o que fica a cargo do programador. Quem conhece os conceitos por trás das decisões aprende uma linguagem nova em dias, lê um programa alheio com segurança e reconhece, em um erro de execução, a regra da linguagem que o explica.

O plano da disciplina{margin}[IME, *Plano de Disciplina 09022, Linguagens de Programação*, Pladis 2025.] fixa dois objetivos. Ilustrar os conceitos que fundamentam as linguagens de programação e os paradigmas que os usam. Comparar os paradigmas. O foco da disciplina é o primeiro objetivo, tomado como uma pergunta sobre significado. Para cada construção, uma declaração, uma atribuição, um laço, uma chamada de função, uma classe, a disciplina pergunta o que ela computa e responde com uma regra. Os paradigmas entram como as famílias em que as construções aparecem, e a sua comparação fica restrita à UD VII. A {numref}[tbl-uds] mostra as sete unidades didáticas e os conceitos de cada uma.

:::table +header
*
  * UD
  * Tema
  * Conceitos
*
  * I
  * Introdução
  * conceitos e paradigmas, sintaxe e semântica, processadores de linguagens
*
  * II
  * Tipos
  * valores e tipos, tipos primitivos, compostos e recursivos, expressões
*
  * III
  * Armazenamento e controle
  * variáveis e atualização, comandos, efeitos colaterais
*
  * IV
  * Abstração
  * funções, parâmetros, avaliação estrita e preguiçosa
*
  * V
  * Encapsulamento
  * tipos abstratos, objetos e classes
*
  * VI
  * Sistemas de tipos
  * sobrecarga, polimorfismo, inferência de tipos, herança
*
  * VII
  * Paradigmas
  * imperativo, orientado a objetos, funcional, lógico
:::

{tabcap "tbl-uds"}[As unidades didáticas da disciplina e os conceitos que cobrem.]

# Sintaxe, Semântica e Pragmática

%%%
tag := "sintaxe-semantica"
%%%

A descrição de uma linguagem de programação tem três partes. A *sintaxe* diz quais sequências de símbolos são programas. A *semântica* diz o que cada programa significa, isto é, o que ele computa. A *pragmática* diz como a linguagem é usada na prática, com que ferramentas e para que fins.

A sintaxe é descrita por uma gramática, e a {secref}[aula-2] a trata em detalhe. A semântica admite várias formas de descrição.{fnref}[semanticas] Esta disciplina usa a *semântica natural*, uma forma de semântica operacional de passo largo em que o significado de cada construção é dado por regras de inferência, e a {secref}[aula-3] a apresenta. A pragmática atravessa as sete unidades, na comparação de C++ com Python, Haskell e Prolog.

A separação entre sintaxe e semântica é a mesma que os alunos conhecem da lógica.{margin}[Disciplina 09006, Lógica Matemática, IME, 3º ano.] Na lógica proposicional, a sintaxe define as fórmulas bem formadas e a semântica atribui a cada fórmula um valor de verdade sob uma valoração. Em uma linguagem de programação, a sintaxe define os programas bem formados e a semântica atribui a cada programa um comportamento.

:::footnotes

{fnAnchor "semanticas"}[] As três famílias clássicas são a semântica operacional, que descreve a execução por regras de transição ou de avaliação, a semântica denotacional, que mapeia cada construção em um objeto matemático, e a semântica axiomática, que descreve o efeito de um comando por asserções sobre o estado antes e depois. Nielson e Nielson apresentam as três sobre uma mesma linguagem imperativa.{margin}[H. R. Nielson e F. Nielson, *Semantics with Applications, A Formal Introduction*, Wiley, 1992, edição revista de 1999.]

:::

# Conceitos

%%%
tag := "conceitos"
%%%

Watt organiza o estudo das linguagens em torno de poucos conceitos, cada um presente, de alguma forma, em quase toda linguagem. A {numref}[tbl-conceitos] os lista com a pergunta que cada um responde e a unidade didática que o trata.

:::table +header
*
  * Conceito
  * Pergunta
  * UD
*
  * Valores e tipos
  * Que dados um programa manipula e como eles se classificam?
  * II
*
  * Armazenamento
  * Como um programa guarda e atualiza dados ao longo da execução?
  * III
*
  * Ligações
  * Como um nome passa a denotar um valor, uma variável ou uma função?
  * III
*
  * Abstração
  * Como um trecho de programa recebe nome e parâmetros para ser reutilizado?
  * IV
*
  * Encapsulamento
  * Como se esconde a representação de um dado atrás de uma interface?
  * V
*
  * Sistemas de tipos
  * Que erros o compilador detecta antes da execução?
  * VI
:::

{tabcap "tbl-conceitos"}[Os conceitos de Watt, a pergunta que cada um responde e a unidade que o trata.]

Um *valor* é um dado que pode ser computado, armazenado, passado a uma função e devolvido por ela. Um *tipo* é um conjunto de valores com as operações que se aplicam a eles. Uma *variável* é uma posição de memória cujo conteúdo muda ao longo da execução. Uma *ligação* associa um identificador a um valor, a uma variável ou a uma função, e o conjunto das ligações em vigor em um ponto do programa é o *ambiente*. Uma *abstração* é um trecho de programa com nome e parâmetros, como uma função ou um procedimento. Um *tipo abstrato de dados* expõe operações e esconde a representação.

Estes conceitos reaparecem, com nomes próprios, na semântica que a disciplina adota. O ambiente é ρ, uma função de identificadores em posições. A memória é σ, uma função de posições em valores. O contexto de tipos é Γ, uma função de identificadores em tipos. Os três entram nas regras desde a UD II e nenhuma regra é reescrita depois.

# Paradigmas

%%%
tag := "paradigmas"
%%%

Um *paradigma* é um estilo de programação caracterizado pelos conceitos que privilegia. Quatro paradigmas organizam a UD VII e atravessam a disciplina.

O paradigma *imperativo* organiza o programa em comandos que atualizam variáveis. O estado da computação é a memória, e o controle é a sequência, a seleção e a repetição. C, Pascal e a parte procedural de C++ são imperativas.

O paradigma *orientado a objetos* organiza o programa em objetos, que guardam estado e respondem a mensagens, e em classes, que descrevem objetos de uma mesma forma. Herança e despacho dinâmico permitem que uma chamada escolha o método pelo objeto receptor. Smalltalk, Java e a parte de classes de C++ são orientadas a objetos.

O paradigma *funcional* organiza o programa em funções, no sentido matemático, e em expressões que as aplicam. Não há atualização de variáveis, e o valor de uma expressão depende só dos valores das suas partes. Haskell, OCaml e Lean são funcionais.

O paradigma *lógico* organiza o programa em fatos e regras, e a execução é a busca de uma prova de uma consulta. Prolog é a linguagem lógica de referência, e os alunos a conhecem da disciplina de Lógica Matemática, com a resolução SLD.

Uma linguagem pode reunir mais de um paradigma. C++ é imperativa, orientada a objetos e, com lambdas e `std::function`, funcional. Python reúne os três. A classificação de uma linguagem por paradigma é uma classificação do estilo que ela favorece, não uma restrição do que ela permite. Para esta disciplina um paradigma é, antes de tudo, um conjunto de construções, e cada construção é estudada pelo significado que tem, independentemente do paradigma que a tornou popular.

# Um Programa em Quatro Paradigmas

%%%
tag := "quatro-paradigmas"
%%%

O fatorial de um número natural serve de comparação. A versão imperativa, em C++, acumula o produto em uma variável ao longo de um laço.

```
int fatorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}
```

A versão funcional, em Haskell, define a função por equações, uma para o caso base e uma para o passo, sem variável e sem laço.

```
fatorial :: Integer -> Integer
fatorial 0 = 1
fatorial n = n * fatorial (n - 1)
```

A versão lógica, em Prolog, define a relação entre um número e o seu fatorial por dois fatos e regras. A consulta `fatorial(5, F)` pede um `F` que satisfaça a relação, e o interpretador o encontra por resolução.

```
fatorial(0, 1).
fatorial(N, F) :-
  N > 0,
  M is N - 1,
  fatorial(M, G),
  F is N * G.
```

A versão em Python é imperativa na forma, mas sem declaração de tipos. O tipo de `acc` é decidido em execução, e um erro de tipo só aparece quando a operação errada é executada.

```
def fatorial(n):
    acc = 1
    for i in range(2, n + 1):
        acc = acc * i
    return acc
```

As quatro versões computam a mesma função. Elas diferem nas construções que usam, um laço e uma atribuição, equações recursivas, uma relação e uma busca, um laço sem tipos declarados. A disciplina estuda o significado de cada uma dessas construções e pergunta, para cada uma, o que ela computa e como uma regra o enuncia. A comparação entre os quatro estilos volta na UD VII, já com o significado de cada construção em mãos.

# Core C++, o Núcleo do Curso

%%%
tag := "core-cpp"
%%%

Em vez de descrever cada conceito em uma linguagem diferente, a disciplina os introduz um a um como construções de uma linguagem núcleo, Core C++, subconjunto de C++17. Todo programa de Core C++ compila com `g++ -std=c++17` e produz o mesmo resultado, então cada regra que a disciplina escreve pode ser confrontada com o compilador. O subconjunto obedece a três princípios.

*Sem comportamento indefinido.* Tudo o que C++17 deixa indefinido, como a divisão por zero, o estouro de `int` e o acesso a uma posição liberada, é excluído pela sintaxe e pela verificação de tipos ou tem o resultado definido `erro` em tempo de execução.

*Semântica determinística.* Onde C++17 admite mais de um resultado, por exemplo na ordem de avaliação dos operandos de `+`, Core C++ fixa um, da esquerda para a direita.

*Gramática LL(1).* A gramática admite análise descendente recursiva com um token de antecipação, com três convenções léxicas que removem as ambiguidades de C++. A {secref}[aula-2] a apresenta.

O programa abaixo é o fatorial em Core C++, igual à versão em C++ da {secref}[quatro-paradigmas], com a função `main` que devolve o fatorial de 5. O interpretador da disciplina, escrito em Lean, o analisa e o executa.

```lean (name := fatorialCore)
def factorial : String :=
  "int fatorial(int n) {
    int acc = 1;
    for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }
    return acc;
  }
  int main() { return fatorial(5); }"

#eval (parseProgram factorial).map run
```
```leanOutput fatorialCore
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

A saída tem dois níveis. O `Except` externo diz que a análise sintática aceitou o texto, e o interno diz que a avaliação terminou em um valor, o inteiro 120. Um erro sintático apareceria no nível externo, e um `erro` de execução, como uma divisão por zero, no interno. A {secref}[aula-4] examina o interpretador como um processador de linguagem.

Core C++ cresce ao longo das unidades. A UD II acrescenta tipos e expressões, a UD III variáveis e comandos, a UD IV funções e lambdas, a UD V classes e a UD VI templates e sobrecarga. O que a disciplina implementou até agora cobre tipos básicos, expressões, comandos e funções de primeira ordem, o suficiente para a UD I e o que a {secref}[aula-3] usa.

# Lean como Linguagem da Semântica

%%%
tag := "lean"
%%%

As regras de tipos e de avaliação de Core C++ são escritas no quadro em semântica natural e codificadas em Lean 4.{margin}[L. de Moura e S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28, LNCS 12699, Springer, 2021.] Lean é uma linguagem de programação funcional com tipos dependentes e um assistente de provas, e a disciplina a usa como linguagem de programação. A sintaxe abstrata é um tipo indutivo, o analisador léxico e o analisador sintático são funções, e cada juízo da semântica é uma função, com a regra que cada caso implementa no comentário. Nenhuma prova em Lean é exigida.

Lean entra em três momentos. Nesta unidade, como demonstração, com o interpretador executando programas e imprimindo árvores de derivação. Em uma sessão de laboratório, na UD III ou IV, em que os alunos acrescentam uma construção pequena ao interpretador. No trabalho da terceira avaliação, em que cada grupo escolhe uma construção, escreve as suas regras no papel, a implementa e a compara com `g++`.

O código do interpretador está no repositório [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp), com um [blueprint](https://christianobraga.github.io/corecpp/) que apresenta cada regra e aponta para a função que a implementa.

# Exercícios

%%%
tag := "exercicios-1"
%%%

{exercise "exr-classificar"}[] Classifique cada linguagem que você já usou pelos paradigmas que ela favorece, e indique uma construção de cada uma que pertence a outro paradigma.

{exercise "exr-conceitos-python"}[] Para a versão em Python do fatorial, diga qual é o ambiente e qual é a memória ao fim da terceira iteração do laço, com `n = 5`.

{exercise "exr-prolog-consulta"}[] Escreva a sequência de consultas que o interpretador Prolog gera ao responder `fatorial(3, F)`, com a regra da {secref}[quatro-paradigmas].

{exercise "exr-haskell-negativo"}[] A versão em Haskell não termina para argumento negativo. Diga por quê e acrescente uma equação que devolva 1 para argumentos negativos, sem alterar as duas equações existentes.

{exercise "exr-core-cpp-main"}[] Escreva em Core C++ uma função `main` que devolve a soma dos inteiros de 1 a 10 e a execute com o interpretador, como no exemplo da {secref}[core-cpp].

```lean -show
end Lecture1
```
