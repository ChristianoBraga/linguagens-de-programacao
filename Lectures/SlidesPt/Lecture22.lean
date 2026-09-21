/-
Slides da Aula 22. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Polimorfismo Paramétrico" =>

Uma declaração, vários tipos, expandida por substituição

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-22___-Polimorfismo-Param___trico/)

```lean -show
namespace Slides22
open CoreCpp
```

# §22.1 Uma declaração, vários tipos

* Uma pilha de `int` e uma pilha de `Point*` são o mesmo programa com uma palavra trocada. Escrever as duas é copiar.

* Um *template de classe* declara a classe uma vez, com o tipo como parâmetro.

* Um parâmetro de tipo no subconjunto, o que a gramática garante.

```lean (name := twoParams)
#eval parseProgram
  "template<typename T> class C { public: T v; };
  int main() { C<int, bool>* p = nullptr; return 0; }"
```
```leanOutput twoParams
Except.error "syntax error at token 23 (','): a class template of this subset has one type parameter"
```

# §22.1 Uma pilha em dois tipos

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

# §22.2 Instanciar é substituir

```tree
p tem template<typename T> class C { … }    C<τ> mencionado em p    C<τ> ∉ tabela de classes de p
────────────────────────────────────────────────────────────────────────────── (Inst)
p ⟶ p, class C<τ> { … [T := τ] … }
```

* Aplicada até o *ponto fixo*, porque a classe que ela acrescenta pode mencionar outra instanciação. Idempotente.

* A substituição alcança todo tipo e todo *nome* de classe, então `Node<T>*` em `Lista<T>` vira `Node<int>*` em `Lista<int>`.

* *Custo*. A expansão precede a execução, então uma classe instanciada é uma classe comum.

* *Verificação*. Um template nunca é verificado, só as suas instanciações são.

# §22.2 Duas instanciações, duas classes

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

* Elas dividem o texto do fonte e mais nada, e não têm relação de subtipo.

# §22.3 O que o parâmetro pode ser

* Qualquer tipo do subconjunto, inclusive outra instanciação.

* O corpo restringe o argumento *sem o dizer*, e o erro aparece na classe expandida.

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

* O `concept` de C++20 existe para enunciar o requisito na declaração, de modo que o erro caia no uso.

# §22.4 Três maneiras de servir a vários tipos

:::table +header
*
  * Abordagem
  * Linguagem
  * O compilador produz
  * O corpo é verificado
*
  * expansão
  * C++, Core C++
  * uma classe por instanciação
  * em cada instanciação
*
  * apagamento
  * Java
  * uma classe, parâmetro apagado
  * uma vez, na declaração
*
  * restringida
  * Haskell, Rust, Ada
  * uma implementação com uma assinatura
  * uma vez, com respeito à restrição
:::

* A expansão dá código rápido, compilações longas e erros tardios. O apagamento dá uma implementação e encaixotamento. Uma restrição dá o erro no uso.

# Resumo

* Um *template de classe* dá uma declaração a uma família de tipos, com um parâmetro de tipo no subconjunto.

* *Inst*. Instanciar é substituir, até o ponto fixo, antes da verificação e antes da execução.

* Uma classe instanciada é uma *classe comum*, então a construção não custa nada em tempo de execução.

* Um template *nunca é verificado*, só as suas instanciações são, e o erro nomeia a classe expandida.

* Expansão, apagamento e implementação restringida são três respostas a uma necessidade.

Exercícios: veja as [notas de aula](../pt/Aula-22___-Polimorfismo-Param___trico/).

```lean -show
end Slides22
```
