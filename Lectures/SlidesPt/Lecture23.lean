/-
Slides da Aula 23. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Subtipagem" =>

Subsunção, os três polimorfismos, e por que dois deles não compõem

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-23___-Subtipagem/)

```lean -show
namespace Slides23
open CoreCpp
```

# §23.1 Subsunção

```tree
Γ ⊢ e : D*    D deriva de B
─────────────────────────────── (T-Sub)
Γ ⊢ e : B*
```

* Do específico para o geral. Quem tem um `Square*` tem um `Shape*`. A recíproca falha.

* Não é um juízo à parte. Ela vive na relação τ ≈ τ', então vale em declarações, atribuições, argumentos, resultados, comparações e ramos de uma vez.

```lean (name := notSuper)
def notSuper : String :=
  "class Shape { public: int side; };
  class Square : public Shape { public: int mark; };
  int main() { Shape* f = new Square(); Square* q = f; return 0; }"

#eval (parseProgram notSuper).map check
```
```leanOutput notSuper
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of q"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Square"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Shape"))))
```

# §23.1 A conversão não faz nada

* Um valor de ponteiro é uma *posição*, e a posição não muda quando o tipo da expressão muda.

* O objeto guarda a sua *etiqueta de classe*, e é assim que o despacho encontra o método da derivada.

* A subsunção acontece em Γ, como a instanciação, e não custa nada em tempo de execução.

```lean (name := dispatch)
def dispatch : String :=
  "class Shape {
  public:
    virtual int area() { return 0; }
    virtual ~Shape() { }
  };
  class Square : public Shape {
  private:
    int side;
  public:
    Square(int l) { this->side = l; }
    int area() override { return side * side; }
  };
  int sum(Shape& f, Shape& g) { return f.area() + g.area(); }
  int main() {
    Shape* a = new Square(3);
    Shape* b = new Square(4);
    int r = sum(*a, *b);
    delete a;
    delete b;
    return r;
  }"

#eval (parseProgram dispatch).map run
```
```leanOutput dispatch
Except.ok (Except.ok (CoreCpp.Val.int 25))
```

# §23.2 Três tipos de polimorfismo

:::table +header
*
  * Tipo
  * O que varia
  * Escolhido
*
  * sobrecarga
  * a declaração que corre
  * em tempo de compilação, pelos tipos dos argumentos
*
  * paramétrico
  * o tipo a que a declaração serve
  * em tempo de compilação, pela instanciação
*
  * inclusão
  * o método que corre
  * em tempo de execução, pela etiqueta de classe
:::

* Sobrecarga, corpos sem relação sob um nome. Paramétrico, um corpo para uma família de tipos. Inclusão, uma interface e um corpo por classe.

* Só a *inclusão* custa algo em tempo de execução, e só ela depende de um valor calculado enquanto o programa corre.

# §23.3 Onde os dois não compõem

* Será `Stack<Square*>` subtipo de `Stack<Shape*>`. Em Core C++, em C++ e em Java, *não*.

```lean (name := invariance)
def invariance : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
    void store(T x) { v = x; }
  };
  class Shape { public: int side; };
  class Square : public Shape { public: int mark; };
  int main() {
    Box<Square*>* c = new Box<Square*>(new Square());
    Box<Shape*>* d = c;
    return 0;
  }"

#eval (parseProgram invariance).map check
```
```leanOutput invariance
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Box<Shape*>"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Box<Square*>"))))
```

# §23.3 Por que a recusa protege o programa

* Se fosse permitida, `d` e `c` nomeariam um objeto de classe `Box<Square*>`.

* `d->store(x)` aceita qualquer `Shape*`, então uma `Shape` comum entraria em uma caixa cujo `get` promete um `Square*`.

* O `c->get()->mark` seguinte leria um campo de um objeto que não o tem.

* *Covariância* em resultados, *contravariância* em parâmetros, *invariância* quando o parâmetro está nos dois, como em `Box`.

* C++ e Core C++ fazem toda instanciação invariante. Java pergunta no uso, Scala e Kotlin na declaração.

# Resumo

* *T-Sub*. Um ponteiro para classe derivada está onde se espera um ponteiro para a base, em toda posição da relação τ ≈ τ'.

* A conversão é um enunciado sobre *tipos*, e a memória não muda, então a etiqueta continua a conduzir o despacho.

* Três polimorfismos, *sobrecarga*, *paramétrico* e *inclusão*, e só o último decide em tempo de execução.

* Duas instanciações de um template são *invariantes*, e a recusa é o que mantém a memória de acordo com os tipos.

Exercícios: veja as [notas de aula](../pt/Aula-23___-Subtipagem/).

```lean -show
end Slides23
```
