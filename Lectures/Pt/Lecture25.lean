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

#doc (Manual) "Aula 25: O Paradigma Imperativo" =>

%%%
tag := "aula-25"
%%%

```lean -show
namespace Lecture25
open CoreCpp
```

Esta aula abre a última unidade, em que os quatro paradigmas são comparados. A comparação repousa sobre um único recurso. Três dos quatro paradigmas são *fragmentos* de Core C++, isto é, a linguagem com algumas construções proibidas, e um fragmento vale a pena porque proibir uma construção compra uma propriedade que a linguagem inteira não tem. A aula define o recurso, dá o fragmento imperativo e enuncia o que a sua restrição compra.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-25.pt.html).*

# Um Paradigma como uma Restrição

%%%
tag := "restricao"
%%%

Um *paradigma* é um estilo de programação caracterizado pelas construções que favorece, como disse a {secref}[aula-1]. Vinte e quatro aulas depois, o curso pode dizer algo mais preciso. Core C++ reúne as construções de três paradigmas ao mesmo tempo, o imperativo, o orientado a objetos e o funcional, então um programa escrito em um desses estilos é um programa de Core C++ que se mantém longe das construções dos outros dois. Essa observação transforma um estilo em um objeto matemático.

Um *fragmento* de Core C++ é um conjunto de construções proibidas. Um programa *pertence* ao fragmento quando nenhuma declaração do programa menciona uma delas.

$$`\dfrac{\text{nenhuma declaração de } p \text{ menciona construção que } f \text{ proíbe}}{p \in f}\;\textsf{(Frag)}`

Três observações fixam o que um fragmento não é. Não é uma gramática, porque nenhuma produção muda, e um programa fora de um fragmento continua um programa de Core C++ com exatamente o significado que as unidades anteriores lhe deram. Não é um sistema de tipos, porque um programa fora de um fragmento não está errado, apenas escrito em outro estilo. E não é uma sublinguagem que o interpretador execute de outra maneira, porque as regras de avaliação também não mudam.

O que muda é o que se pode *dizer* de um programa. As regras de Core C++ admitem `erro` de oito maneiras, e um fragmento que proíbe `delete` elimina três delas para todo programa que lhe pertence. As regras deixam a ordem de avaliação de `f() + g()` a uma escolha, e um fragmento sem atribuição torna a escolha invisível. O resto desta unidade é essa troca, um paradigma de cada vez, proíba isto e ganhe aquilo.

O predicado é uma varredura da sintaxe abstrata, e o interpretador o executa.

```lean (name := fragCheck)
def gcd : String :=
  "int gcd(int a, int b) {
    while (b != 0) { int t = b; b = a % b; a = t; }
    return a;
  }
  int main() { int x = gcd(48, 18); int& y = x; y = y + 1; return y; }"

#eval (parseProgram gcd).map (fragment .imperative)
```
```leanOutput fragCheck
Except.ok (Except.ok ())
```

# O Fragmento Imperativo

%%%
tag := "imperativo"
%%%

O fragmento imperativo conserva o que as quatro primeiras unidades construíram e nada mais. A {numref}[tbl-imperative] lista os dois lados.

:::table +header
*
  * Admite
  * Proíbe
*
  * `int`, `bool`, `void`
  * tipos classe, ponteiro, vetor e função
*
  * variáveis, declaração com inicializador, `auto`
  * `new`, `delete`
*
  * a referência local `τ& y = e`, a atribuição
  * `this`, acesso a campo, desreferência, indexação
*
  * bloco, `if`, `while`, `for`, `return`, expressão como comando
  * chamada de método, classe, template de classe
*
  * funções de primeira ordem, por valor e por referência
  * lambda, `std::function`, chamada por valor de função
:::

{tabcap "tbl-imperative"}[O que o fragmento imperativo admite e o que proíbe.]

O programa da {secref}[restricao] pertence ao fragmento, e é um programa imperativo comum, um laço com duas variáveis, uma função, uma referência local e uma atribuição.

```lean (name := mdcRun)
#eval (parseProgram gcd).map run
```
```leanOutput mdcRun
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

Um programa que declara uma classe não pertence ao fragmento, e o verificador nomeia a construção e a declaração em que ela ocorre.

```lean (name := fragReject)
def comClasse : String :=
  "class C { public: int v; };
   int main() { C* c = new C(); return c->v; }"

#eval (parseProgram comClasse).map (fragment .imperative)
```
```leanOutput fragReject
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class C" })
```

O vetor também é proibido, o que merece uma palavra, porque um vetor não é um objeto no sentido usual do paradigma. Core C++ não tem arranjo, então a única sequência que oferece é `std::vector`, e a única forma de obter uma é `new`. Admitir o vetor admitiria, portanto, o monte, e o monte é exatamente o que a próxima seção diz que o fragmento não tem. O preço é que um programa imperativo do fragmento não tem dado composto, e o curso o paga de olhos abertos.

```lean (name := fragVector)
def comVetor : String :=
  "int main() {
     std::vector<int>* v = new std::vector<int>(2);
     return 0;
   }"

#eval (parseProgram comVetor).map (fragment .imperative)
```
```leanOutput fragVector
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "pointer type", site := "function main" })
```

# O Que a Restrição Compra

%%%
tag := "pilha"
%%%

A linguagem inteira aloca posições de duas maneiras. Uma declaração e uma ligação de parâmetro alocam uma cada, e as duas são liberadas quando o bloco ou a chamada que as fez termina. Um `new` aloca tantas quantos campos um objeto tem, e só um `delete` as libera. O fragmento imperativo não tem `new`, então resta a primeira maneira, e a memória vira uma pilha.

Seguem três enunciados, todos por inspeção das regras que o fragmento admite, nenhum deles uma prova em Lean.

*Todo valor de σ é básico.* Os valores de Core C++ são `int`, `bool`, `void`, uma posição, `null`, um objeto, um vetor e um closure. O fragmento não tem construção que produza qualquer um dos cinco últimos. Uma declaração guarda o valor do seu inicializador, uma expressão do fragmento, e toda regra de expressão do fragmento produz um `int` ou um `bool`.

*A memória segue uma disciplina de pilha.* Lendo as regras `Decl`, `Block` e `Call` juntas, uma posição entra em σ em uma declaração ou em uma ligação de parâmetro e sai na saída do bloco ou da chamada que é o seu escopo, na ordem inversa da entrada. Nada mais toca o domínio de σ.

*Uma posição pendente é inalcançável.* Uma expressão do fragmento alcança uma posição de um só modo, por ρ, pela regra `LocVar`. Como ρ liga um nome apenas enquanto a posição vive, o resultado `erro` por `danglingLocation` não pode ocorrer. Dois dos oito resultados `erro` de Core C++ desaparecem com ele, o `delete` duplo e o acesso depois do `delete`, e o `delete` por ponteiro para a base desaparece com as classes.

Essa é a forma de toda afirmação desta unidade. O fragmento é menor, então menos regras se aplicam, então mais se pode dizer.

Uma leitura honesta também nomeia o que o fragmento perde. Sem o monte, nenhuma estrutura de dados sobrevive à função que a construiu, então um programa imperativo do fragmento computa sobre o que cabe nas suas variáveis. É por isso que o fragmento orientado a objetos da {secref}[aula-26] existe, e por isso que C, a linguagem imperativa por excelência, tem ponteiros.

# Controle

%%%
tag := "controle"
%%%

A outra metade do paradigma é o controle. O fragmento imperativo herda as três formas da {secref}[aula-11], a sequência, a seleção e a repetição, e a regra `While-T`, que recorre à própria conclusão, é a que dá significado ao laço. Um programa do fragmento é, portanto, lido como uma sequência de mudanças de estado no tempo, e o seu significado é a memória final.

Vale contrastar isso com a {secref}[aula-27]. Lá, a mesma computação é um termo cujo valor não depende do tempo, e o laço vira uma chamada recursiva. As duas leituras se encontram na mesma semântica, com o mesmo ρ e o mesmo σ, que é a razão de ter escrito um só conjunto de regras para a linguagem inteira.

# Exercícios

%%%
tag := "exercicios-25"
%%%

{exercise "exr-frag-classify"}[] Execute as três verificações de fragmento sobre todo programa de `examples/` e monte a tabela de qual exemplo pertence a qual fragmento. Dois deles não pertencem a nenhum. Diga que construções os põem fora dos três.

{exercise "exr-frag-argue"}[] Dê um programa do fragmento imperativo cuja memória final tenha quatro posições, e dê a ordem em que elas entram e saem de σ. Confirme com `bin/corecpp trace`.

{exercise "exr-frag-error"}[] Dos oito resultados `erro` de Core C++, diga quais um programa do fragmento imperativo ainda pode produzir, e dê um programa para cada.

{exercise "exr-frag-reference"}[] A referência local é admitida no fragmento imperativo e proibida no funcional. Justifique as duas decisões a partir da propriedade que cada fragmento reivindica.

{exercise "exr-frag-vector"}[] Suponha que Core C++ tivesse o arranjo `int a[10]`, com o arranjo vivendo no quadro da sua declaração. Diga quais dos três enunciados da {secref}[pilha] sobreviveriam se o fragmento imperativo o admitisse, e quais precisariam de um argumento novo.

{exercise "exr-frag-extend"}[] Escreva o conjunto de construções proibidas de um fragmento que admite o monte mas não a classe, isto é, `new std::vector<int>` e ponteiros para vetores mas nenhuma classe definida pelo usuário. Enuncie uma propriedade que esse fragmento tem e o orientado a objetos não.

```lean -show
end Lecture25
```
