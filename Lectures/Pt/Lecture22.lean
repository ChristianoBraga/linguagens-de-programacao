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

#doc (Manual) "Aula 22: Polimorfismo Paramétrico" =>

%%%
tag := "aula-22"
%%%

```lean -show
namespace Lecture22
open CoreCpp
```

A sobrecarga dá um nome a várias declarações escritas à mão. Esta aula dá uma declaração a vários tipos, o que é o *polimorfismo paramétrico*. Um template de classe é uma classe com um parâmetro de tipo, e cada instanciação é uma classe que o compilador escreve por substituição. A aula dá a regra da instanciação, mostra um template usado em dois tipos, e compara a construção com os genéricos de outras linguagens, em que a mesma ideia se realiza de outra maneira.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-22.pt.html).*

# Uma Declaração, Vários Tipos

%%%
tag := "uma-declaracao"
%%%

A pilha da {secref}[aula-17] guarda inteiros. Uma pilha de ponteiros para `Point` seria o mesmo programa com `int` trocado por `Point*` em toda parte, e escrevê‑la de novo é copiar. A repetição não é só trabalhosa, é um problema de manutenção, porque uma correção em uma cópia precisa ser feita nas outras.

Um *template de classe* declara a classe uma vez, com o tipo como parâmetro.

```lean (name := stack)
def stack : String :=
  "template<typename T>
  class Stack {
  private:
    std::vector<T>* items;
    int top;
  public:
    Stack(int n) {
      this->items = new std::vector<T>(n);
      this->top = 0;
    }
    void push(T x) { (*items)[top] = x; top = top + 1; }
    T pop() { top = top - 1; return (*items)[top]; }
    bool empty() { return top == 0; }
  };
  class Point { public: int x; };
  int main() {
    Stack<int>* p = new Stack<int>(4);
    p->push(3);
    p->push(4);
    int s = p->pop() + p->pop();
    Stack<Point*>* q = new Stack<Point*>(2);
    Point* a = new Point();
    a->x = 35;
    q->push(a);
    return s + q->pop()->x;
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

A declaração menciona `T` onde a classe de inteiros mencionava `int`, no tipo do vetor, no parâmetro de `push` e no resultado de `pop`. Os usos em `main` escrevem `Stack<int>` e `Stack<Point*>`, e cada um deles é um tipo como outro qualquer.

O parâmetro é um parâmetro de *tipo*, e o subconjunto admite um, o que a gramática garante.

```lean (name := twoParams)
#eval parseProgram
  "template<typename T> class C { public: T v; };
  int main() { C<int, bool>* p = nullptr; return 0; }"
```
```leanOutput twoParams
Except.error "syntax error at token 23 (','): a class template of this subset has one type parameter"
```

# Instanciar É Substituir

%%%
tag := "instanciacao"
%%%

O significado de um template é dado por uma regra que age sobre o programa, antes de os juízos de tipagem e de avaliação o verem.

```
p tem template<typename T> class C { … }    C<τ> mencionado em p    C<τ> ∉ tabela de classes de p
────────────────────────────────────────────────────────────────────────────── (Inst)
p ⟶ p, class C<τ> { … [T := τ] … }
```

Lendo a regra da esquerda para a direita, um programa que menciona `Stack<int>` e ainda não tem uma classe com esse nome ganha uma, o corpo do template com `int` no lugar de `T`. A regra se aplica de novo enquanto faltar alguma instanciação mencionada, então um template cujo corpo menciona outro template também é expandido, e o processo para quando nenhuma instanciação falta. Ela é idempotente, então aplicá‑la duas vezes não acrescenta nada, o que permite ao verificador de tipos e ao interpretador aplicá‑la cada um por si.

A substituição alcança todo tipo do corpo, e também os nomes das classes que ele menciona, então um `Node<T>*` dentro de uma `Lista<T>` vira um `Node<int>*` dentro de `Lista<int>`. O nome de uma instanciação é o texto que o projeto imprime para o tipo, então o nome no fonte e o nome da classe expandida são a mesma cadeia, e as mensagens do verificador nomeiam a classe que o programador escreveu.

Duas consequências importam para o resto do curso. A primeira é o *custo*. A expansão acontece antes de o programa correr, então uma classe instanciada é uma classe comum e a chamada de um seu método é uma chamada de método comum. Nada do parâmetro sobrevive na memória nem na derivação, e um programa que usa `Stack<int>` corre exatamente como a classe escrita à mão da {secref}[aula-17]. A segunda é a *verificação*. Um template nunca é verificado, só as suas instanciações são, e um template que ninguém instancia nunca é olhado. C++ faz o mesmo em substância, com uma primeira fase que verifica o que não depende do parâmetro, que o subconjunto deixa de fora.

```lean (name := instantiated)
def instantiated : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
  };
  int main() { return 0; }"

#eval (parseProgram instantiated).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiated
Except.ok (Except.ok [])
```

Um template sozinho expande para nada, porque o programa não menciona instanciação alguma. Mencionar uma produz a classe.

```lean (name := instantiatedTwo)
def instantiatedTwo : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
  };
  int main() {
    Box<int>* a = new Box<int>(40);
    Box<bool>* b = new Box<bool>(true);
    return a->get() + (b->get() ? 2 : 0);
  }"

#eval (parseProgram instantiatedTwo).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiatedTwo
Except.ok (Except.ok ["Box<int>", "Box<bool>"])
```

```lean (name := instantiatedRun)
#eval (parseProgram instantiatedTwo).map run
```
```leanOutput instantiatedRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

As duas instanciações são duas classes, com dois vetores próprios e dois conjuntos de métodos. Elas dividem o texto do fonte e mais nada. Em particular não têm relação como tipos, o que a {secref}[aula-23] retoma, e um erro no corpo aparece uma vez por instanciação.

A instanciação de um nome que não é template é um erro da expansão, relatado antes de qualquer tipagem.

```lean (name := notTemplate)
#eval (parseProgram
  "int main() { Stack<int>* p = new Stack<int>(2); return 0; }").map check
```
```leanOutput notTemplate
Except.ok (Except.error (CoreCpp.TypeError.instantiation
   "Stack is not a class template, in the instantiation Stack<int>"))
```

# O Que o Parâmetro Pode Ser

%%%
tag := "parametro"
%%%

O argumento de uma instanciação é um tipo do subconjunto, um tipo básico, um ponteiro, um vetor ou uma classe, inclusive outra instanciação. Um template pode, portanto, ser usado em um tipo que não existia quando ele foi escrito, o que é o objetivo da construção.

O corpo restringe o argumento sem o dizer. Uma `Stack<T>` guarda os seus elementos em um `std::vector<T>`, e um elemento de vetor precisa de valor por omissão, então `T` precisa ser um tipo que tenha um. Um template cujo corpo compara dois `T` com `<` exige um `T` que `<` aceite. Nada na declaração registra esses requisitos, e o erro aparece na instanciação, dentro da classe expandida, o que é a fraqueza conhecida da construção.{margin}[B. Stroustrup, *Concepts, The Future of Generic Programming*, ISO WG21 paper N4361, 2015.]

```lean (name := badInstance)
def badInstance : String :=
  "template<typename T>
  class Pair {
  public:
    T a;
    T b;
    bool sorted() { return a < b; }
  };
  class Point { public: int x; };
  int main() {
    Pair<Point*>* p = new Pair<Point*>();
    return p->sorted() ? 1 : 0;
  }"

#eval (parseProgram badInstance).map check
```
```leanOutput badInstance
Except.ok (Except.error (CoreCpp.TypeError.badOperand "<" (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Point"))))
```

A mensagem nomeia o operador e o tipo, e aponta para dentro da classe expandida, não para dentro do template. C++ produz mensagem do mesmo tipo, bem mais longa, e o `concept` de C++20 existe para enunciar o requisito na declaração, de modo que o erro possa ser relatado no uso.

# Comparação com Outras Linguagens

%%%
tag := "comparacao"
%%%

A mesma necessidade, uma declaração servindo a vários tipos, é atendida de três maneiras nas linguagens correntes, e a diferença aparece no que o compilador produz e em quando o erro surge. A {numref}[tbl-generics] as compara.

:::table +header
*
  * Abordagem
  * Linguagem
  * O que o compilador produz
  * Quando o corpo é verificado
*
  * expansão por substituição
  * C++, Core C++
  * uma classe por instanciação
  * em cada instanciação
*
  * uma implementação, apagada
  * Java, desde a versão 5
  * uma classe, o parâmetro apagado para `Object`
  * uma vez, na declaração
*
  * uma implementação, restringida
  * Haskell, Rust, Ada
  * uma implementação, com uma assinatura que o parâmetro precisa satisfazer
  * uma vez, com respeito à restrição
:::

{tabcap "tbl-generics"}[Três maneiras de dar uma declaração a vários tipos.]

A expansão produz código rápido, porque cada instanciação é especializada e nada é decidido em tempo de execução, e produz compilações longas e erros tardios. O apagamento produz uma implementação e verifica o corpo uma vez, ao preço de encaixotar os valores e de perder o parâmetro em tempo de execução. Uma implementação restringida enuncia na declaração o que o parâmetro precisa oferecer, verifica o corpo uma vez com respeito a esse enunciado, e relata erro no uso quando o argumento não o satisfaz, o que é o melhor dos dois para o leitor e o que mais exige da linguagem.

Core C++ segue C++ porque o curso lê C++, e a regra `Inst` é o relato mais curto e honesto do que `template` significa lá.

# Exercícios

%%%
tag := "exercicios-22"
%%%

{exercise "exr-template-queue"}[] Transforme a fila dos exercícios da {secref}[aula-17] em um template, instancie‑a em `int` e em um ponteiro para uma classe sua, e rode um programa que usa as duas.

{exercise "exr-template-expansion"}[] Para um template seu, imprima a tabela de classes antes e depois da expansão com `Templates.instantiate`, e diga qual menção do programa produziu cada classe.

{exercise "exr-template-nested"}[] Escreva um template `Lista<T>` cujo corpo menciona `Node<T>`, ele próprio um template, e verifique pela tabela de classes que a expansão chega a um ponto fixo. Diga quantas classes a tabela tem para `Lista<int>`.

{exercise "exr-template-error"}[] Escreva um template cujo corpo é correto para `int` e errado para um ponteiro, instancie‑o nos dois, e mostre que a mensagem nomeia a classe expandida. Diga em uma frase o que um `concept` teria mudado.

{exercise "exr-template-erasure"}[] Explique como seria a memória de um programa se Core C++ apagasse o parâmetro como Java faz, e que verificação o verificador de tipos teria de acrescentar em cada uso de `pop`.

{exercise "exr-template-cost"}[] Dê dois programas que usam `Stack<int>`, um com o template e outro com a classe escrita à mão da {secref}[aula-17], e compare as suas derivações. Diga o que na derivação mostra que instanciar não custa nada em tempo de execução.

```lean -show
end Lecture22
```
