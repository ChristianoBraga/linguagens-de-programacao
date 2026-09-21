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

#doc (Manual) "Aula 27: O Paradigma Funcional" =>

%%%
tag := "aula-27"
%%%

```lean -show
namespace Lecture27
open CoreCpp
```

O fragmento funcional proíbe a atualização. Conserva as expressões, os lambdas, os valores de função e as chamadas, e abre mão da atribuição, dos laços e do monte. O que ele compra é a mais forte das três propriedades, a memória é escrita uma única vez, e dela decorrem duas consequências que o resto da linguagem não tem, a transparência referencial e a indiferença à ordem de avaliação. A aula enuncia as duas, escreve o estudo de caso da unidade no fragmento, e usa Haskell como contraste onde Core C++ para.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-27.pt.html).*

# O Fragmento

%%%
tag := "fragmento-funcional"
%%%

A {numref}[tbl-functional] dá os dois lados.

:::table +header
*
  * Admite
  * Proíbe
*
  * `int`, `bool`, `void`, `std::function`
  * a atribuição
*
  * literais, variável, operadores, o condicional
  * `while`, `for`, expressão como comando
*
  * chamada de função, chamada por valor de função
  * a referência local, o parâmetro por referência
*
  * o lambda `[=]`
  * classe, template de classe, chamada de método, `this`
*
  * declaração com inicializador, `auto`
  * `new`, `delete`, acesso a campo, desreferência, indexação
*
  * bloco, `if`, `return`
  * tipos ponteiro, vetor e classe
:::

{tabcap "tbl-functional"}[O que o fragmento funcional admite e o que proíbe.]

A declaração sobrevive, e vale dizer por quê. No fragmento, uma declaração não é uma variável no sentido imperativo, é uma *ligação*, um nome para o valor de uma expressão, porque nada pode escrever a posição depois. O laço não sobrevive, então um programa do fragmento itera por recursão, e a expressão como comando também não, já que sem atualização ela só poderia estar ali por um efeito que o fragmento não tem.

```lean (name := funCheck)
def scale : String :=
  "int sum(int n) {
     return n == 0 ? 0 : n + sum(n - 1);
   }
   std::function<int(int)> scale(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int apply(std::function<int(int)> f, int v) {
     return f(v);
   }
   int main() {
     std::function<int(int)> triple = scale(3);
     int s = sum(4);
     return apply(triple, s);
   }"

#eval (parseProgram scale).map fun p => (fragment .functional p, run p)
```
```leanOutput funCheck
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

O programa tem uma função recursiva, uma função que devolve um closure e uma função que recebe um, que entre elas são o paradigma inteiro. Um laço ou uma atribuição põem um programa fora do fragmento, e o verificador diz em que declaração.

```lean (name := funNoLoop)
def comLaco : String :=
  "int f(int n) {
     int a = 0;
     for (int i = 0; i < n; i = i + 1) { a = a + i; }
     return a;
   }
   int main() { return f(3); }"

#eval (parseProgram comLaco).map (fragment .functional)
```
```leanOutput funNoLoop
Except.ok (Except.error { frag := CoreCpp.Frag.functional, what := "for", site := "function f" })
```

```lean (name := funNoAssign)
def comAtrib : String :=
  "int main() { int x = 1; x = x + 1; return x; }"

#eval (parseProgram comAtrib).map (fragment .functional)
```
```leanOutput funNoAssign
Except.ok (Except.error { frag := CoreCpp.Frag.functional, what := "assignment", site := "function main" })
```

# A Memória É Escrita uma Vez

%%%
tag := "escrita-unica"
%%%

A linguagem inteira escreve σ em uma posição em três lugares, a regra `Assign`, o construtor que um `new` executa e o destrutor que um `delete` executa. O fragmento não tem nenhum dos três. Uma posição recebe, portanto, o seu valor na declaração ou na ligação de parâmetro que a criou, pelas regras `Decl` e `Call`, e nenhuma regra do fragmento a escreve de novo.

Chame isso de *escrita única*. Não é o mesmo que dizer que σ não muda, porque uma chamada ainda aloca posições para os seus parâmetros e as libera no retorno. É o enunciado mais forte e mais útil de que nenhuma posição guarda dois valores diferentes na sua vida.

Seguem duas consequências, ambas por inspeção das regras que o fragmento admite.

*Transparência referencial.* Avaliar uma expressão duas vezes sob o mesmo ρ e o mesmo σ dá o mesmo valor. O argumento é que o valor de uma expressão é determinado pelos valores das posições que as suas variáveis livres denotam, que essas posições vivem o tempo todo, e que a escrita única diz que os seus valores não mudam. A leitura prática é que um nome pode ser trocado pelo que denota, que é a licença de que toda simplificação algébrica de um programa funcional precisa.

*Indiferença à ordem de avaliação.* A {secref}[aula-12] fixou a ordem dos operandos de `e₁ ⊕ e₂` da esquerda para a direita, porque uma chamada dentro de um operando pode mudar σ e C++17 deixa a escolha ao compilador. No fragmento, nenhum operando pode mudar σ em uma posição que o outro lê, então as duas ordens dão o mesmo resultado, e a escolha torna‑se invisível. Um programa do fragmento tem, portanto, um só significado sob Core C++ e sob qualquer compilador C++, que é a forma mais nítida do acordo que o curso busca desde a {secref}[aula-4].

O preço é que o fragmento não exprime computação sobre estrutura de dados, por não ter monte, e não exprime atualização no lugar de forma alguma. Uma linguagem funcional responde à primeira com estruturas imutáveis, listas e árvores construídas uma vez e compartilhadas, e à segunda recusando a pergunta. Core C++ não a pode seguir até lá, porque um objeto de Core C++ é sempre um registro mutável de posições, e o enunciado honesto é que o fragmento é o paradigma em miniatura.

# Recursão no Lugar da Iteração

%%%
tag := "recursao"
%%%

Sem o laço, uma repetição é uma chamada recursiva, e a correspondência é exata. Um laço com acumulador vira uma função com parâmetro acumulador, e o invariante do laço vira a especificação da função. O estudo de caso da unidade o mostra, com o filtro passado como valor de função.

```lean (name := caseFun)
def caseFun : String :=
  "int sumTo(std::function<bool(int)> p, int n) {
     return n == 0 ? 0 : (p(n) ? n : 0) + sumTo(p, n - 1);
   }
   int main() {
     std::function<bool(int)> even = [=](int i) -> bool { return i % 2 == 0; };
     return sumTo(even, 10);
   }"

#eval (parseProgram caseFun).map fun p => (fragment .functional p, run p)
```
```leanOutput caseFun
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

As duas versões do estudo de caso, esta e a orientada a objetos da {secref}[aula-26], põem o ponto de extensão em lugares diferentes. Aqui o critério é um argumento, então um critério novo é um valor novo no sítio da chamada e `sumTo` não muda. Lá é um método `virtual`, então um critério novo é uma classe nova e `add` não muda. As duas são a mesma liberdade de projeto, gasta em moeda diferente.

Um custo da forma recursiva aparece na derivação. Cada chamada aloca as posições dos seus parâmetros e as libera no retorno, então uma recursão de profundidade dez põe dez quadros em σ ao mesmo tempo, onde o laço reaproveita um. Uma linguagem funcional responde com a eliminação de chamada em cauda, que Core C++ não tem e o curso não reivindica.

# Onde Core C++ Para, e Haskell Segue

%%%
tag := "haskell"
%%%

Três coisas que uma linguagem funcional oferece ficam fora de Core C++, e o curso as mostra em Haskell em vez de fingir que o núcleo as tem.

*Dados imutáveis.* Uma lista em Haskell é construída uma vez e compartilhada, então uma função que acrescenta um elemento devolve uma lista nova que compartilha a antiga, e a escrita única vale para os dados tanto quanto para as posições. O fragmento não tem dado algum, e essa é a lacuna.

*Preguiça.* A {secref}[aula-16] deu a passagem por nome como uma regra sem contraparte no núcleo, e Haskell avalia por necessidade, então um argumento é avaliado no máximo uma vez e só se for usado. É isso que permite a um programa Haskell definir uma lista infinita e tomar dez elementos dela.

*Tipos algébricos e casamento de padrão.* Um tipo soma com um `case` é como uma linguagem funcional escreve o que Core C++ escreve com hierarquia de classes e despacho. A comparação é a da {secref}[aula-23], e as duas são duais, uma é fácil de estender com casos novos e difícil com operações novas, a outra ao contrário.

Nenhuma das três muda a semântica que o curso escreveu. Elas são a razão de o paradigma merecer uma linguagem própria em vez de um fragmento de outra, e dizê‑lo com clareza é mais útil do que esticar Core C++ para imitá‑las.

# Exercícios

%%%
tag := "exercicios-27"
%%%

{exercise "exr-fun-iterative"}[] Escreva o fatorial no fragmento funcional, com parâmetro acumulador, e dê o invariante do laço da versão imperativa como a especificação da sua função.

{exercise "exr-fun-order"}[] Dê dois programas, um no fragmento funcional e outro fora dele, em que `f() + g()` tenha um valor no primeiro e dois valores possíveis em C++ para o segundo. Diga que regra do fragmento exclui o segundo caso.

{exercise "exr-fun-transparency"}[] Tome o estudo de caso e troque `even` pelo próprio lambda no sítio da chamada. Argumente, a partir da escrita única, que os dois programas têm o mesmo valor, e confirme com o interpretador.

{exercise "exr-fun-depth"}[] Imprima a derivação de `sumTo(even, 3)` e conte as posições vivas em σ no ponto mais profundo. Diga quantas a versão com laço da {secref}[aula-25] tem no seu ponto mais profundo.

{exercise "exr-fun-capture"}[] O lambda do estudo de caso não captura nada. Escreva um que capture um limite do escopo envolvente, e explique, pela regra `Lambda`, por que a captura não pode quebrar a escrita única.

{exercise "exr-fun-haskell"}[] Escreva o estudo de caso em Haskell com `filter` e `sum`, e diga quais das três coisas da {secref}[haskell] a sua versão usa.

```lean -show
end Lecture27
```
