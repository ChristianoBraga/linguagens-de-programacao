/-
Slides da Aula 1. Cada seção de nível superior é um slide. O código Lean
é elaborado na construção e coincide com o das notas de aula.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Linguagens e Paradigmas" =>

Conceitos, paradigmas e o núcleo Core C++

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-1___-Linguagens-e-Paradigmas/)

Estrutura de D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990.

```lean -show
namespace Slides1
open CoreCpp
```

# §1.1 Por que estudar linguagens de programação?

* Cada linguagem fixa decisões sobre *valores, tipos, memória, controle e abstração*.

* As decisões determinam o que é fácil de expressar, o que o compilador verifica e o que fica com o programador.

* Quem conhece os conceitos aprende uma linguagem nova em dias e reconhece, em um erro, a regra que o explica.

* Objetivos do plano de disciplina. *Ilustrar* os conceitos e os paradigmas que os usam. *Comparar* os paradigmas.

* Foco da disciplina. O *significado de cada construção*. O que computa uma declaração, uma atribuição, um laço, uma chamada? Uma *regra* responde. A comparação de paradigmas fica na UD VII.

# §1.1 As sete unidades

:::table +header
*
  * UD
  * Tema
  * Conceitos
*
  * I
  * Introdução
  * conceitos, sintaxe, semântica, processadores
*
  * II
  * Tipos
  * valores, tipos primitivos, compostos, recursivos
*
  * III
  * Armazenamento e controle
  * variáveis, comandos, efeitos colaterais
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
  * sobrecarga, polimorfismo, inferência, herança
*
  * VII
  * Paradigmas
  * imperativo, orientado a objetos, funcional, lógico
:::

# §1.2 Sintaxe, semântica e pragmática

* *Sintaxe*. Quais sequências de símbolos são programas. Descrita por uma gramática.

* *Semântica*. O que cada programa significa. Nesta disciplina, *semântica natural*, regras de inferência que dizem o que cada construção computa.

* *Pragmática*. Como a linguagem é usada, com que ferramentas e para que fins.

* A separação é a mesma da lógica. Fórmulas bem formadas e valorações lá, programas bem formados e comportamentos aqui.

# §1.3 Os conceitos de Watt

:::table +header
*
  * Conceito
  * Pergunta
*
  * Valores e tipos
  * Que dados um programa manipula e como se classificam?
*
  * Armazenamento
  * Como um programa guarda e atualiza dados?
*
  * Ligações
  * Como um nome passa a denotar um valor, uma variável ou uma função?
*
  * Abstração
  * Como um trecho recebe nome e parâmetros para ser reutilizado?
*
  * Encapsulamento
  * Como se esconde a representação atrás de uma interface?
*
  * Sistemas de tipos
  * Que erros o compilador detecta antes da execução?
:::

# §1.3 Os conceitos na semântica

* Ambiente *ρ*, uma função de identificadores em posições.

* Memória *σ*, uma função de posições em valores.

* Contexto de tipos *Γ*, uma função de identificadores em tipos.

* Os três entram nas regras desde a UD II. *Nenhuma regra é reescrita depois.* Só entram regras novas.

# §1.4 Paradigmas

* *Imperativo*. Comandos que atualizam variáveis. C, Pascal, a parte procedural de C++.

* *Orientado a objetos*. Objetos com estado e classes que os descrevem. Herança e despacho dinâmico. Smalltalk, Java, as classes de C++.

* *Funcional*. Funções no sentido matemático e expressões que as aplicam. Sem atualização. Haskell, OCaml, Lean.

* *Lógico*. Fatos e regras, e a execução é a busca de uma prova. Prolog, com a resolução SLD de Lógica Matemática.

* Uma linguagem reúne paradigmas. A classificação descreve o *estilo que ela favorece*.

# §1.5 O fatorial em C++ e em Haskell

::::cols
:::col
{lbl}[Imperativo, C++]

```
int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}
```
:::
:::col
{lbl}[Funcional, Haskell]

```
fatorial :: Integer -> Integer
fatorial 0 = 1
fatorial n = n * fatorial (n - 1)
```
:::
::::

# §1.5 O fatorial em Prolog e em Python

::::cols
:::col
{lbl}[Lógico, Prolog]

```
fatorial(0, 1).
fatorial(N, F) :-
  N > 0,
  M is N - 1,
  fatorial(M, G),
  F is N * G.
```
:::
:::col
{lbl}[Imperativo sem tipos declarados, Python]

```
def factorial(n):
    acc = 1
    for i in range(2, n + 1):
        acc = acc * i
    return acc
```
:::
::::

* A mesma função, quatro conjuntos de construções. A disciplina estuda o *significado de cada construção*, e a comparação volta na UD VII.

# §1.6 Core C++, o núcleo do curso

* Um subconjunto de C++17. Todo programa compila com `g++ -std=c++17` e produz o mesmo resultado.

* *Sem comportamento indefinido*. O que C++ deixa indefinido é excluído pela sintaxe e pelos tipos ou vira o resultado `erro`.

* *Determinístico*. Onde C++ admite mais de um resultado, Core C++ fixa um, da esquerda para a direita.

* *Gramática LL(1)*, com três convenções léxicas que removem as ambiguidades de C++.

* Cresce ao longo das unidades. Tipos e expressões, comandos, funções e lambdas, classes, templates.

# §1.6 O fatorial em Core C++, executado

```lean (name := factorialCore)
def factorial : String :=
  "int factorial(int n) {
    int acc = 1;
    for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }
    return acc;
  }
  int main() { return factorial(5); }"

#eval (parseProgram factorial).map run
```
```leanOutput factorialCore
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

* O `Except` externo é a análise sintática, o interno é a avaliação.

# §1.7 Lean como linguagem da semântica

* As regras vão ao quadro em *semântica natural* e ao computador em *Lean 4*.

* Sintaxe abstrata como tipo indutivo, analisadores como funções, um juízo por função, uma regra por caso, com a regra no comentário.

* Três momentos. *Demonstração* na UD I. *Laboratório* na UD III ou IV. *Trabalho* da terceira avaliação.

* Nenhuma prova em Lean é exigida.

* Código em [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp), blueprint em [christianobraga.github.io/corecpp](https://christianobraga.github.io/corecpp/).

# Resumo

* Uma linguagem é um conjunto de decisões sobre *valores, memória, ligações, abstração, encapsulamento e tipos*.

* *Sintaxe* diz o que é programa, *semântica* diz o que ele computa, *pragmática* diz como se usa.

* Quatro *paradigmas*, imperativo, orientado a objetos, funcional e lógico, cada um uma família de construções. A disciplina estuda o *significado de cada construção*.

* *Core C++* é o núcleo do curso, sem comportamento indefinido, determinístico e LL(1).

* A semântica é escrita em regras e codificada em *Lean*, e o interpretador executa os programas do núcleo.

Exercícios: veja as [notas de aula](../pt/Aula-1___-Linguagens-e-Paradigmas/).

```lean -show
end Slides1
```
