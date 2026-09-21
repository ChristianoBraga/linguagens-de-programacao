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

#doc (Manual) "Aula 12: Expressões com Efeitos Colaterais" =>

%%%
tag := "aula-12"
%%%

```lean -show
namespace Lecture12
open CoreCpp
```

Esta aula fecha a UD III com a interação entre expressões e memória. Uma expressão tem um *efeito colateral* quando a sua avaliação muda a memória, e em Core C++ isso acontece só por uma chamada de função. A aula mostra por que a ordem de avaliação passa a fazer parte do significado quando há efeitos, enuncia as ordens que Core C++ fixa, as contrasta com o que C++17 deixa ao compilador, e revê o fragmento inteiro da linguagem implementado até esta unidade.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-12.pt.html).*

# Efeitos por Chamadas

%%%
tag := "efeitos"
%%%

Uma expressão da UD I não tem efeito. As suas regras levam a memória pelas premissas, ρ, σ ⊢ e ⇒ v, σ', mas toda regra devolve a memória que recebeu, e a ordem dos operandos não importa para o valor. A {secref}[aula-8] mostrou a primeira expressão com efeito, uma chamada a uma função que escreve por um ponteiro. A função `next` abaixo incrementa um contador alcançado pelo seu parâmetro e devolve o valor novo.

```lean (name := proxDef)
def counter : String :=
  "class Cell { public: int n; };
   int next(Cell* c) {
     c->n = c->n + 1;
     return c->n;
   }
   int main() {
     Cell* c = new Cell();
     return next(c) + 10 * next(c);
   }"

#eval (parseProgram counter).map run
```
```leanOutput proxDef
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

As duas chamadas devolvem valores diferentes, 1 e 2, porque a memória muda entre elas. A soma é 1 + 10 · 2 = 21 quando a chamada da esquerda executa primeiro, e 2 + 10 · 1 = 12 quando a da direita executa primeiro. O valor da expressão depende da ordem de avaliação, e a ordem faz parte, portanto, do significado de `+`.

# As Ordens que Core C++ Fixa

%%%
tag := "ordens"
%%%

Core C++ fixa uma ordem para cada construção, e as regras a carregam na ordem das suas premissas. A {numref}[tbl-ordens] as lista.

:::table +header
*
  * Construção
  * Ordem
  * Regra
  * Em C++17
*
  * `e₁ ⊕ e₂`
  * operando esquerdo, depois o direito
  * `Binary`
  * não especificada
*
  * `f(e₁, …, eₖ)`
  * argumentos da esquerda para a direita
  * `Call`
  * não especificada
*
  * `e₁ = e₂`
  * lado direito, depois o esquerdo
  * `Assign`
  * direito antes do esquerdo
*
  * `e[i]`
  * vetor, depois o índice
  * `LocIndex`
  * objeto antes do índice
*
  * `e₁ && e₂`, `e₁ || e₂`
  * esquerdo, depois o direito só se preciso
  * `And`, `Or`
  * a mesma
*
  * `e₁ ? e₂ : e₃`
  * condição, depois o ramo escolhido
  * `Cond`
  * a mesma
:::

{tabcap "tbl-ordens"}[As ordens de avaliação de Core C++ e a sua situação em C++17.]

As duas primeiras linhas são decisões de Core C++ onde C++17 não toma nenhuma. A norma diz que os operandos de `+` e os argumentos de uma chamada são avaliados em ordem não especificada, e um compilador pode escolher qualquer ordem, e até uma diferente em cada ocorrência. As quatro últimas linhas são ordens que C++17 fixa, e Core C++ as mantém. A atribuição avalia o lado direito primeiro desde C++17, uma mudança em relação às normas anteriores feita para remover uma classe de resultados não especificados.

A regra `Binary` é a que carrega a primeira decisão. As suas premissas leem ρ, σ ⊢ e₁ ⇒ v₁, σ₁ e depois ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂. A segunda premissa parte da memória que a primeira produziu, e a ordem das premissas é a ordem de avaliação.

```
ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

# A Derivação Alternativa

%%%
tag := "alternativa"
%%%

Um compilador C++ que avalia o operando direito primeiro aplica uma regra que Core C++ não tem.

```
ρ, σ ⊢ e₂ ⇒ v₂, σ₁    ρ, σ₁ ⊢ e₁ ⇒ v₁, σ₂    v₁ ⊕ v₂ = v
──────────────────────────────────────────────────────── (Binary-RL)
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂
```

Sob `Binary-RL` o programa da {secref}[efeitos] devolve 12. As duas derivações são válidas para C++17, e a norma não escolhe. Uma linguagem cuja semântica tem as duas regras é *não determinística*, um programa pode ter dois resultados, e um programa correto precisa produzir o mesmo resultado sob as duas, uma obrigação de prova que a norma deixa ao programador.

Core C++ tem uma regra e um resultado, a propriedade que a {secref}[aula-3] chamou de determinismo. O preço é uma diferença em relação a C++ que a disciplina enuncia uma vez. Um programa de Core C++ com duas chamadas com efeito em uma expressão tem o valor que Core C++ lhe dá, e um compilador C++ pode lhe dar outro. O exemplo `call_order.cpp` do repositório devolve 21 sob o interpretador, e devolve 21 ou 12 sob `g++`, conforme a versão e as opções.

A atribuição mostra a ordem fixada em ação. O lado direito é avaliado primeiro, então `next(c)` devolve 1 ali, e o índice do lado esquerdo é avaliado depois e devolve 2.

```lean (name := assignOrder)
def assignOrder : String :=
  "class Cell { public: int n; };
   int next(Cell* c) { c->n = c->n + 1; return c->n; }
   int main() {
     Cell* c = new Cell();
     std::vector<int>* v = new std::vector<int>(3);
     (*v)[next(c)] = next(c);
     return (*v)[1] * 10 + (*v)[2];
   }"

#eval (parseProgram assignOrder).map run
```
```leanOutput assignOrder
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

O elemento de índice 2 recebe 1, o elemento de índice 1 mantém o seu valor por omissão 0, e o resultado é 0 · 10 + 1. Sob a ordem de C++14 e anteriores o mesmo programa poderia guardar 2 no índice 1.

Os argumentos de uma chamada seguem a mesma disciplina. O primeiro argumento é avaliado primeiro, e o segundo vê a memória que o primeiro deixou.

```lean (name := callOrder)
def callOrder : String :=
  "class Cell { public: int n; };
   int next(Cell* c) { c->n = c->n + 1; return c->n; }
   int f(int a, int b) { return a * 10 + b; }
   int main() {
     Cell* c = new Cell();
     return f(next(c), next(c));
   }"

#eval (parseProgram callOrder).map run
```
```leanOutput callOrder
Except.ok (Except.ok (CoreCpp.Val.int 12))
```

# Por que Não Proibir Efeitos em Expressões

%%%
tag := "por-que-nao"
%%%

Uma linguagem pode evitar a questão inteira proibindo chamadas com efeito dentro de expressões, ou proibindo efeitos de todo, como faz uma linguagem funcional pura. Core C++ os mantém por duas razões. A primeira é a fidelidade a C++, em que uma chamada em uma expressão é comum. A segunda é que as regras já têm tudo de que precisam. A memória foi levada pelo juízo de expressão desde a {secref}[aula-3], precisamente para que uma chamada dentro de uma expressão pudesse mudá‑la, e nenhuma regra desta unidade foi reescrita para admitir efeitos. A decisão da {secref}[aula-3] de escrever ρ, σ ⊢ e ⇒ v, σ' e não ρ, σ ⊢ e ⇒ v compensa aqui.

O que as regras fixam é a ordem, e essa é a lição da unidade. Um efeito colateral não é um defeito da semântica, é uma característica da linguagem que a semântica precisa descrever por completo, e descrevê‑la por completo é escolher uma ordem onde a linguagem a deixa em aberto.

# O Fragmento até Aqui

%%%
tag := "fragmento-12"
%%%

Três unidades construíram o fragmento seguinte de Core C++, todo ele no interpretador e no [blueprint](https://christianobraga.github.io/corecpp/) da linguagem. Tipos `int`, `bool`, `void`, classes com campos, ponteiros para classes e para vetores, e `std::vector<τ>`. Expressões com literais, variáveis, os operadores aritméticos, relacionais e lógicos, o condicional, `new`, acesso a campo, desreferência, indexação e chamadas. Comandos com declaração, declaração de referência, atribuição, bloco, `if`, `while`, `for` e `return`. Funções com chamada por valor. Vinte e três programas de exemplo, cada um compilando com `g++` para o código de saída que o interpretador computa, ou para um resultado indefinido onde Core C++ dá `erro`.

A UD IV acrescenta as construções de abstração. Parâmetros por referência, que reutilizam a regra `DeclRef` na chamada. Lambdas e `std::function`, que fazem de uma função um valor com ambiente próprio. E a comparação entre chamada por valor, por referência e por nome, a última com Haskell como linguagem de contraste.

# Exercícios

%%%
tag := "exercicios-12"
%%%

{exercise "exr-duas-ordens"}[] Para o programa da {secref}[efeitos], construa as duas derivações, uma com `Binary` e uma com `Binary-RL`, até a soma, e mostre onde as memórias diferem.

{exercise "exr-ordem-irrelevante"}[] Dê uma condição sobre as funções chamadas em `f(x) + g(y)` sob a qual as duas ordens produzem o mesmo valor e a mesma memória final, e argumente pelas regras que a condição basta.

{exercise "exr-atribuicao-antiga"}[] Escreva a regra de atribuição de C++14, em que a ordem dos dois lados não é especificada, como duas regras, e dê um programa de Core C++ que produz duas memórias finais diferentes sob elas.

{exercise "exr-argumentos"}[] Escreva a regra `Call-RL` que avalia os argumentos da direita para a esquerda e compute, sob ela, o resultado do programa da {secref}[alternativa] que chama `f(next(c), next(c))`.

{exercise "exr-fragmento-puro"}[] Identifique o maior subconjunto das expressões de Core C++ em que a ordem de avaliação é irrelevante, e prove, por indução nas regras, que nele ρ, σ ⊢ e ⇒ v, σ' implica σ' = σ.

{exercise "exr-tres-efeitos"}[] Escreva um programa de Core C++ em que uma expressão contém três chamadas com efeito, preveja o seu valor pelas regras, e confira com o interpretador e com `g++`. Relate se `g++` concordou e explique por que qualquer dos dois desfechos é consistente com C++17.

```lean -show
end Lecture12
```
