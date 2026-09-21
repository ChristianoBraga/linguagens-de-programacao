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

#doc (Manual) "Aula 17: Tipos Abstratos de Dados" =>

%%%
tag := "aula-17"
%%%

```lean -show
namespace Lecture17
open CoreCpp
```

Esta aula abre a UD V com a pergunta de como um programa esconde a representação de um dado atrás das operações que o usam. Um *tipo abstrato de dados* é um conjunto de valores conhecido só por uma assinatura de operações, e uma classe com uma seção `public` e uma seção `private` é a construção que C++ oferece para escrevê‑lo. A aula enuncia a visibilidade como regra de tipos de Core C++, apresenta a tabela de classes que o verificador mantém e escreve a regra que torna uma classe bem formada. Objetos, construtores e chamadas de método recebem as suas regras de avaliação na {secref}[aula-18].

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-17.pt.html).*

# Representação e Assinatura

%%%
tag := "assinatura"
%%%

Uma pilha de inteiros é conhecida por quatro operações. Criar uma pilha vazia de uma dada capacidade, empilhar um valor, desempilhar o último valor empilhado e perguntar se a pilha está vazia. Um programa que usa uma pilha não precisa de mais nada, e em particular não precisa saber que os valores ficam em um vetor com um contador para a próxima posição livre. As operações formam a *assinatura* do tipo, e o vetor e o contador formam a sua *representação*.{margin}[B. Liskov e S. Zilles, *Programming with Abstract Data Types*, ACM SIGPLAN Notices 9(4), 1974, pp. 50 a 59.]

Separar as duas tem uma consequência que Parnas enunciou para módulos em geral.{margin}[D. L. Parnas, *On the Criteria To Be Used in Decomposing Systems into Modules*, Communications of the ACM 15(12), 1972, pp. 1053 a 1058.] Quem usa o tipo depende só da assinatura, então a representação pode mudar, de um vetor para uma lista encadeada por exemplo, sem alteração alguma nos programas que a usam. A assinatura é um contrato, e a representação é uma decisão privada de quem implementa.

Em Core C++ um tipo abstrato de dados é uma `class` com duas seções. A seção `public` guarda a assinatura, os métodos que um cliente chama, e a seção `private` guarda a representação, os campos que só os métodos alcançam.

```lean (name := stack)
def stack : String :=
  "class Stack {
  private:
    std::vector<int>* items;
    int top;
  public:
    Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
    void push(int x) { (*items)[top] = x; top = top + 1; }
    int pop() { top = top - 1; return (*items)[top]; }
    bool empty() { return top == 0; }
  };
  int main() {
    Stack* p = new Stack(8);
    p->push(1);
    p->push(41);
    return p->pop() + p->pop();
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

O cliente, a função `main`, cria uma pilha, empilha dois valores e os desempilha. Ele nunca menciona `items` nem `top`. O construtor `Stack(int n)` roda quando `new Stack(8)` cria o objeto e dá aos campos os primeiros valores, e cada método lê e escreve os campos por `this`, ou pelo nome do campo sozinho, que dentro de um método denota o campo de `this`.

# A Visibilidade como Regra de Tipos

%%%
tag := "visibilidade"
%%%

A separação é imposta antes de o programa rodar. Um cliente que alcança a representação é rejeitado pelo verificador de tipos, então o contrato não é uma convenção, e sim uma regra da linguagem.

```lean (name := peek)
def peek : String :=
  "class Stack {
  private:
    std::vector<int>* items;
    int top;
  public:
    Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
  };
  int main() { Stack* p = new Stack(8); return p->top; }"

#eval (parseProgram peek).map check
```
```leanOutput peek
Except.ok (Except.error (CoreCpp.TypeError.privateMember "Stack" "top"))
```

A regra é uma premissa de todo acesso a um membro. Dentro de um corpo de membro o contexto de tipos Γ liga `this` a um ponteiro para a classe, e a *classe corrente* é a classe de `this`. Um membro privado declarado na classe $`K` é visível exatamente quando a classe corrente é $`K`.

```
C tem τ f declarado em K    f público ou Γ(this) = K*
──────────────────────────────────────────────────── (Visible)
```

Toda regra que alcança um membro, acesso a campo, acesso por seta e chamada de método, carrega essa premissa. Fora de toda classe Γ não tem `this`, então só membros públicos são visíveis, e dentro dos métodos de $`K` todo membro de $`K` é. Uma classe derivada não vê os membros privados da sua base, porque dentro dos seus métodos `this` tem a classe derivada, e não $`K`, a mesma regra que C++ aplica.{fnref}[protected]

:::footnotes

{fnAnchor "protected"}[] C++ tem uma terceira seção, `protected`, cujos membros são visíveis na classe e nas suas derivadas. Core C++ mantém só `public` e `private`, e uma classe derivada alcança o estado da sua base pelos métodos públicos da base. O projeto também deixa de fora as declarações `friend`, que concedem visibilidade a uma função ou classe nomeada, e os membros `static`, que pertencem à classe e não aos seus objetos.

:::

# A Tabela de Classes

%%%
tag := "tabela-de-classes"
%%%

O verificador de tipos mantém uma *tabela de classes*, uma função finita de nomes de classe em declarações. Uma declaração tem uma classe base opcional, os seus campos e métodos com a visibilidade, no máximo um construtor e no máximo um destrutor. A {numref}[tbl-class-table] lista o que a tabela responde.

:::table +header
*
  * Pergunta
  * Resposta
  * Lean
*
  * a cadeia de uma classe
  * a classe, a sua base, a base da base, até a raiz
  * `Program.chain`
*
  * os campos de um objeto
  * todo campo da cadeia, a base raiz primeiro, com a classe que o declara
  * `Program.allFields`
*
  * um método de uma classe
  * a declaração mais próxima com esse nome na cadeia, com a classe que a declara
  * `Program.findMethod`
*
  * se $`D` deriva de $`B`
  * $`B` está na cadeia de $`D`
  * `Program.subclass`
*
  * um destrutor virtual
  * alguma classe da cadeia declara um
  * `Program.hasVirtualDtor`
:::

{tabcap "tbl-class-table"}[As perguntas que a tabela de classes responde e as funções de `Syntax.lean` que as calculam.]

A mesma tabela serve ao avaliador, que a consulta quando `new` aloca os campos de um objeto e quando `delete` os libera, e quando uma chamada de método resolve o método a executar. Herança e despacho são o assunto da {secref}[aula-19].

# Uma Classe Bem Formada

%%%
tag := "bem-formada"
%%%

Uma classe é bem formada quando a sua declaração satisfaz a regra `T-Class`, uma conjunção de verificações sobre a forma da classe e sobre os corpos dos seus membros.

```
B existe e a cadeia de C não tem ciclo
os campos têm tipos com valores, bem formados, e não repetem campo de uma base
os membros têm nomes distintos
cada método que redefine um método de uma base o encontra virtual lá, leva override e mantém a assinatura
o construtor de B, se existe, não tem parâmetros
[this ↦ C*, x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'   para o corpo c de cada método, do construtor e do destrutor
───────────────────────────────────────────────────────────────────────────────────────────────── (T-Class)
⊢ class C : public B { … }
```

A premissa sobre os corpos é a que importa para o tipo abstrato de dados. O corpo de um método é verificado sob um contexto que liga `this` a $`C*` e os parâmetros aos seus tipos, com o tipo de retorno do método como tipo do `return`. Um construtor e um destrutor têm `void` como tipo de retorno. Dentro desses corpos os campos da classe são alcançáveis pela regra `T-VarField` da {secref}[aula-18], e os privados são visíveis porque a classe corrente é $`C`.

A premissa sobre o construtor da base existe porque Core C++ não tem listas de inicialização, a sintaxe `D() : B(x) { }` de C++ que passa argumentos ao construtor da base. Os construtores de uma cadeia rodam da base raiz para baixo, o da classe criada com os argumentos de `new` e os demais sem, então uma base com construtor parametrizado não pode ser derivada. A premissa sobre métodos redefinidos é o assunto da {secref}[aula-19].

# Invariantes de Representação

%%%
tag := "invariantes"
%%%

Uma representação em geral satisfaz uma propriedade que toda operação preserva, o *invariante de representação*. Para a pilha, o contador `top` fica entre zero e a capacidade do vetor, e os valores abaixo de `top` são os empilhados e ainda não desempilhados. A visibilidade é o que torna o invariante demonstrável. Como só os métodos escrevem os campos, verificar que cada método preserva a propriedade, supondo que ela vale na entrada, basta para saber que ela vale em todo ponto de todo cliente.

Core C++ torna visível uma consequência de um invariante quebrado. A pilha acima não verifica os seus limites, e um cliente que empilha nove valores em uma pilha de capacidade oito faz `push` escrever no índice oito de um vetor de tamanho oito. Em C++ essa escrita é comportamento indefinido. Em Core C++ ela é o resultado `erro`, pela regra `LocIndex` da {secref}[aula-7], e o programa para na operação que quebrou o contrato. Uma pilha que confere `top` com a capacidade, e reporta o estouro ao cliente por um resultado `bool`, mantém o invariante por conta própria.

# Exercícios

%%%
tag := "exercicios-17"
%%%

{exercise "exr-queue"}[] Escreva uma classe `Fila` com a assinatura de uma fila, enfileirar, desenfileirar e vazia, sobre um vetor e dois contadores, com os contadores privados. Enuncie o seu invariante de representação.

{exercise "exr-visibility-derived"}[] Escreva uma classe `Base` com um campo privado e uma classe `Derivada : public Base` cujo método lê esse campo, rode o verificador de tipos e explique a mensagem pela regra `Visible`.

{exercise "exr-swap-representation"}[] Reescreva a pilha da {secref}[assinatura] sobre uma lista encadeada de objetos `Node` em vez de um vetor, mantendo a assinatura. Confira que a função `main` do exemplo roda sem alteração.

{exercise "exr-invariant-check"}[] Mude `push` para devolver um `bool`, falso quando a pilha está cheia, e explique por que o invariante então vale para todo cliente, com a regra que de outro modo produziria `erro`.

{exercise "exr-class-table"}[] Para as classes da {secref}[assinatura], escreva a tabela de classes como o verificador a vê, e o contexto Γ sob o qual o corpo de `pop` é verificado.

{exercise "exr-tclass"}[] Dê uma classe que viole cada premissa de `T-Class` por vez, rode o verificador em cada uma e associe a mensagem à premissa.

```lean -show
end Lecture17
```
