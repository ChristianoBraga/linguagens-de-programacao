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

* Uma pilha de `int` e uma pilha de `Ponto*` são o mesmo programa com uma palavra trocada. Escrever as duas é copiar.

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
  class Pilha {
  private:
    std::vector<T>* itens;
    int topo;
  public:
    Pilha(int n) {
      this->itens = new std::vector<T>(n);
      this->topo = 0;
    }
    void empilha(T x) { (*itens)[topo] = x; topo = topo + 1; }
    T desempilha() { topo = topo - 1; return (*itens)[topo]; }
    bool vazia() { return topo == 0; }
  };
  class Ponto { public: int x; };
  int main() {
    Pilha<int>* p = new Pilha<int>(4);
    p->empilha(3);
    p->empilha(4);
    int s = p->desempilha() + p->desempilha();
    Pilha<Ponto*>* q = new Pilha<Ponto*>(2);
    Ponto* a = new Ponto();
    a->x = 35;
    q->empilha(a);
    return s + q->desempilha()->x;
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

* A substituição alcança todo tipo e todo *nome* de classe, então `No<T>*` em `Lista<T>` vira `No<int>*` em `Lista<int>`.

* *Custo*. A expansão precede a execução, então uma classe instanciada é uma classe comum.

* *Verificação*. Um template nunca é verificado, só as suas instanciações são.

# §22.2 Duas instanciações, duas classes

```lean (name := instantiatedTwo)
def instantiatedTwo : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
  };
  int main() {
    Caixa<int>* a = new Caixa<int>(40);
    Caixa<bool>* b = new Caixa<bool>(true);
    return a->abre() + (b->abre() ? 2 : 0);
  }"

#eval (parseProgram instantiatedTwo).map fun p =>
  (Templates.instantiate p).map fun q => q.classes.map (·.name)
```
```leanOutput instantiatedTwo
Except.ok (Except.ok ["Caixa<int>", "Caixa<bool>"])
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
  class Par {
  public:
    T a;
    T b;
    bool ordenado() { return a < b; }
  };
  class Ponto { public: int x; };
  int main() {
    Par<Ponto*>* p = new Par<Ponto*>();
    return p->ordenado() ? 1 : 0;
  }"

#eval (parseProgram badInstance).map check
```
```leanOutput badInstance
Except.ok (Except.error (CoreCpp.TypeError.badOperand "<" (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Ponto"))))
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
