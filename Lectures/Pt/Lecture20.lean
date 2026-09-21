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

#doc (Manual) "Aula 20: Orientação a Objetos" =>

%%%
tag := "aula-20"
%%%

```lean -show
namespace Lecture20
open CoreCpp
```

Esta aula fecha a UD V. Ela olha a orientação a objetos como um modo de organizar um programa em torno das construções das três aulas anteriores, o `namespace` como agrupamento de classes, a compilação separada como o idioma de C++ para o tipo abstrato de dados, e os processos de desenvolvimento que o plano de disciplina pede para discutir. O último assunto não tem regras. A aula termina com o fragmento de Core C++ implementado até esta unidade.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-20.pt.html).*

# Namespaces

%%%
tag := "namespaces"
%%%

Um programa com muitas classes precisa de um modo de agrupá‑las e de manter os seus nomes separados. Um `namespace N { … }` agrupa classes sob o prefixo `N::`, e um cliente as nomeia pelo nome qualificado.

```lean (name := ns)
def ns : String :=
  "namespace Bank {
    class Account {
    private:
      int balance;
    public:
      Account(int initial) { balance = initial; }
      void deposit(int v) { balance = balance + v; }
      int query() { return balance; }
    };
  }
  int main() {
    Bank::Account* c = new Bank::Account(100);
    c->deposit(20);
    return c->query();
  }"

#eval (parseProgram ns).map run
```
```leanOutput ns
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

O `namespace` não acrescenta regra de tipos nem de avaliação. O analisador o achata, então a tabela de classes recebe uma classe chamada `Bank::Account` e toda regra trabalha sobre esse nome.

```lean (name := nsNames)
#eval (parseProgram ns).map fun p => p.classes.map (·.name)
```
```leanOutput nsNames
Except.ok ["Bank::Account"]
```

Dentro do `namespace` um nome de classe não qualificado denota a classe do próprio `namespace`, então o construtor `Account(int)` e um campo de tipo `Account*` não precisam de prefixo ali. Core C++ mantém só isto do `namespace` de C++. Não há `using`, não há funções nem variáveis dentro de um `namespace`, e não há modo de alcançar uma classe de um escopo envolvente de dentro de um `namespace` a não ser pelo nome qualificado.{fnref}[nested]

:::footnotes

{fnAnchor "nested"}[] Os `namespace` se aninham, e uma classe declarada em `namespace A { namespace B { … } }` chama‑se `A::B::C`. A regra dos nomes não qualificados dentro de um `namespace` os resolve para o `namespace` mais interno, `A::B::C`, e uma classe de `A` é alcançada de dentro de `B` como `A::C`. C++ resolve um nome não qualificado procurando nos escopos envolventes de dentro para fora, e Core C++ simplifica essa busca a um escopo.

:::

# Orientação a Objetos

%%%
tag := "oo"
%%%

As construções da UD V, classes com visibilidade, objetos com identidade em σ, construtores, despacho e herança, são o vocabulário do paradigma *orientado a objetos*, um dos quatro da {secref}[aula-1]. O paradigma organiza um programa como um conjunto de objetos que guardam estado e respondem a chamadas de método, e permite a um cliente trabalhar com um objeto por um tipo base enquanto a classe do próprio objeto decide o que cada chamada faz. O que o paradigma favorece pode ser lido nas regras.

*Encapsulamento.* A regra `Visible` da {secref}[aula-17] confina a representação aos métodos. Um cliente vê uma assinatura, e um invariante de representação é preservado verificando só os métodos.

*Identidade e estado.* Um objeto é um registro de posições em σ, {secref}[aula-6], alcançado por ponteiros. Dois ponteiros para a mesma posição nomeiam o mesmo objeto, alterações por um são vistas pelo outro, e um objeto sobrevive ao bloco que o criou. É o modelo de uma entidade mutável com identidade, o oposto da semântica de valores da UD II, em que dois inteiros iguais são indistinguíveis.

*Substitutibilidade.* A regra `Subsumption` da {secref}[aula-19] permite a um cliente escrito para `Shape*` receber um `Square*`. Toda operação da assinatura de `Shape` se aplica ao objeto, então o cliente funciona sem alteração para toda classe que deriva de `Shape`, inclusive classes escritas depois do cliente.{margin}[B. Meyer, *Object-Oriented Software Construction*, 2ª ed., Prentice Hall, 1997, capítulos 14 e 16.]

*Ligação tardia.* A premissa sobre `virtual` em `MethodCall` decide o método pelo objeto, e não pelo ponteiro. Um cliente que chama `f->area()` não precisa saber que forma tem em mãos, e a escolha é feita em tempo de execução, a cada chamada.

Cook observa que um tipo abstrato de dados e um objeto diferem em onde vivem as operações.{margin}[W. R. Cook, *On Understanding Data Abstraction, Revisited*, Proceedings of OOPSLA 2009, pp. 557 a 572.] Um tipo abstrato de dados tem uma representação e operações que a veem, como a pilha da {secref}[aula-17], cujos métodos leem o vetor e o contador do receptor e de qualquer outra pilha que lhes seja passada. Um objeto expõe só a sua assinatura, mesmo a outros objetos da mesma classe, então dois objetos podem ter representações diferentes atrás da mesma assinatura, como `Square` e um hipotético `Circulo` atrás de `Shape`. Core C++ oferece os dois, e a diferença é de projeto, não de linguagem.

# Compilação Separada

%%%
tag := "separada"
%%%

Programas em C++ de qualquer tamanho são divididos em arquivos. Um *cabeçalho* `.hh` declara uma classe, os seus campos e as assinaturas dos seus métodos, e um *fonte* `.cpp` define os métodos com a sintaxe qualificada `Stack::push`. Os clientes incluem o cabeçalho e nunca veem o fonte. O compilador traduz cada fonte em um arquivo objeto, e o ligador os junta em um programa.

```
// stack.hh
class Stack {
private:
  std::vector<int>* items;
  int top;
public:
  Stack(int n);
  void push(int x);
  int pop();
  bool empty();
};

// stack.cpp
#include "stack.hh"
Stack::Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
void Stack::push(int x) { (*items)[top] = x; top = top + 1; }
int Stack::pop() { top = top - 1; return (*items)[top]; }
bool Stack::empty() { return top == 0; }
```

A compilação separada é o idioma de C++ para o tipo abstrato de dados na escala dos arquivos. O cabeçalho é a assinatura, o fonte é a representação das operações, e uma alteração no fonte não obriga os clientes a recompilar, só a religar. Ela se apoia no pré‑processador, `#include`, e na definição de métodos fora da classe, e Core C++ não tem nenhum dos dois. O projeto mantém um programa como um arquivo e uma unidade de tradução, porque o idioma não acrescenta regra de tipos nem de avaliação às da {secref}[aula-17] e da {secref}[aula-18]. O cabeçalho ainda expõe os campos privados, já que o compilador precisa do tamanho de um objeto, e o tipo totalmente opaco exige o idioma do ponteiro para a implementação, uma classe cujo único campo é um ponteiro para uma classe privada definida no fonte.

# Processos de Desenvolvimento

%%%
tag := "processos"
%%%

O plano de disciplina lista orientação a objetos e processos de desenvolvimento juntos, e a ligação é o tipo abstrato de dados. Uma assinatura fixada antes da sua representação é uma unidade de trabalho que pode ser especificada, implementada, testada e substituída por conta própria, e todo processo de desenvolvimento desde Parnas organizou o trabalho em torno dessas unidades.

Um processo *sequencial* fixa os requisitos, depois o projeto, depois escreve o código e o testa, cada fase alimentando a seguinte. Royce descreveu essa sequência e advertiu, no mesmo artigo, que uma passagem única raramente funciona e que o projeto precisa ser revisto depois dos testes.{margin}[W. W. Royce, *Managing the Development of Large Software Systems*, Proceedings of IEEE WESCON, 1970, pp. 1 a 9.] Um processo *iterativo* constrói o programa em ciclos curtos, cada um entregando software em funcionamento para uma parte dos requisitos, e as assinaturas das classes são o que permite entregar uma parte antes de o resto existir. O desenvolvimento *dirigido por testes* escreve o teste de uma assinatura antes da sua implementação, e o teste é um cliente do tipo abstrato de dados.{margin}[K. Beck, *Test-Driven Development, By Example*, Addison-Wesley, 2002.]

Em todo processo a classe é a unidade que muda de mãos. A sua assinatura é o que a equipe acorda, a sua representação é o que um desenvolvedor possui, e os seus testes são o que diz aos dois que o contrato vale. As regras desta unidade são a razão de o contrato ser confiável. A visibilidade torna a representação inalcançável, então um teste da assinatura testa tudo o que um cliente pode fazer.

# O Fragmento da UD V

%%%
tag := "fragmento-20"
%%%

A {numref}[tbl-fragment-20] lista as construções que a UD V acrescentou a Core C++, com as regras de cada uma. A especificação do fragmento é `spec-ud5.md`, e o capítulo do blueprint sobre encapsulamento aponta cada regra para a função Lean que a implementa.

:::table +header
*
  * Construção
  * Tipos
  * Avaliação
*
  * classe com seções, base, construtor e destrutor
  * `T-Class`
  * a tabela de classes
*
  * membro privado
  * `Visible`
  * nenhuma, a visibilidade é estática
*
  * `this`, membro não qualificado
  * `T-This`, `T-VarField`
  * `This`, `LocVarField`
*
  * `new C(args)`
  * `T-New`
  * `New`, os construtores da raiz para baixo
*
  * `e->m(args)`, `e.m(args)`
  * `T-MethodArrow`, `T-Method`
  * `MethodCall`, `Member`, despacho pela etiqueta quando virtual
*
  * `D* ≈ B*`
  * `Subsumption`
  * nenhuma, a etiqueta nunca muda
*
  * `delete e`
  * `T-Delete`, `T-DeleteVec`
  * `Delete`, `DeleteVec`, `DeleteNull`, os destrutores da etiqueta para cima
*
  * `namespace N`
  * nenhuma, achatado pelo analisador
  * nenhuma
:::

{tabcap "tbl-fragment-20"}[As construções da UD V e as suas regras.]

Três propriedades do fragmento merecem registro. Todo objeto continua a viver em σ do `new` ao `delete` ou ao fim do programa, e nunca é copiado, então o modelo da UD II se mantém. O despacho estático e o dinâmico concordam em todo método não virtual, pela restrição sobre redefinição. Os três comportamentos indefinidos de C++17 em torno de `delete`, o `delete` duplo, o acesso após `delete` e o `delete` por ponteiro para a base sem destrutor virtual, são `erro` em Core C++, pelas regras da {secref}[aula-19].

# Exercícios

%%%
tag := "exercicios-20"
%%%

{exercise "exr-ns-nested"}[] Escreva dois `namespace`, um aninhado no outro, cada um com uma classe, e um `main` que cria um objeto de cada. Imprima a tabela de classes com `Program.classes` e explique os nomes.

{exercise "exr-adt-vs-object"}[] Acrescente à pilha da {secref}[aula-17] um método `igual(Stack* outra)` que compara duas pilhas lendo os campos de `outra`. Explique, com a distinção de Cook, por que esse método é possível para um tipo abstrato de dados e não seria para um objeto conhecido só pela assinatura.

{exercise "exr-substitution"}[] Escreva uma função que recebe um `Shape*` e devolve o dobro da sua área, e a chame com um `Square*` e com um `Shape*`. Explique, por `Subsumption` e `MethodCall`, por que uma função serve aos dois.

{exercise "exr-header"}[] Divida o programa da {secref}[namespaces] em um cabeçalho e um fonte em C++ real, compile com `g++` e descreva que alteração no fonte obriga o cliente a recompilar e qual não obriga.

{exercise "exr-tdd"}[] Escreva, antes de implementá‑la, um `main` que testa uma classe `Conjunto` com as operações inserir, contém e tamanho sobre um vetor, com o resultado esperado no valor de retorno. Depois implemente a classe até o teste passar no interpretador e no `g++`.

{exercise "exr-fragment-review"}[] Para cada linha da {numref}[tbl-fragment-20], escreva um programa de no máximo seis linhas aceito pelo verificador de tipos e um rejeitado, e nomeie a regra que o rejeita.

```lean -show
end Lecture20
```
