/-
Slides da Aula 19. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Herança e Despacho" =>

Subsunção, métodos virtuais, destrutores e delete

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-19___-Heran___a-e-Despacho/)

```lean -show
namespace Slides19
open CoreCpp
```

# §19.1 Herança simples

```lean (name := shapes)
def shapes : String :=
  "namespace Geometry {
    class Shape {
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
  }
  int main() {
    Geometry::Shape* f = new Geometry::Square(4);
    int a = f->area();
    delete f;
    return a;
  }"

#eval (parseProgram shapes).map run
```
```leanOutput shapes
Except.ok (Except.ok (CoreCpp.Val.int 16))
```

* Subsunção, despacho e um destrutor virtual, em um programa.

# §19.2 Subsunção

```tree
D deriva de B
────────────────── (Subsumption)
D* ≈ B*
```

* Vale onde quer que ≈ apareça. Declarações, atribuições, argumentos, retornos, comparações, `?:`.

* A única conversão entre tipos de classe. A direção oposta é erro de tipo.

```lean (name := downcast)
def downcast : String :=
  "class Base { public: int x; };
  class Derived : public Base { public: int y; };
  int main() { Base* b = new Derived(); Derived* d = b; return 0; }"

#eval (parseProgram downcast).map check
```
```leanOutput downcast
Except.ok (Except.error (CoreCpp.TypeError.mismatch
   "initialiser of d"
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Derived"))
   (CoreCpp.Ty.ptr (CoreCpp.Ty.cls "Base"))))
```

# §19.2 Tipo estático e etiqueta de classe

* O verificador de tipos conhece o *tipo estático*, `Shape*`.

* O avaliador vê a *etiqueta de classe* do objeto em σ, `Square`.

* Os dois podem diferir em todo ponto do programa. O *despacho* decide qual governa uma chamada de método.

# §19.3 Despacho

```lean (name := staticDyn)
def staticDyn : String :=
  "class Base {
  public:
    int fixed() { return 1; }
    virtual int dispatched() { return 10; }
  };
  class Derived : public Base {
  public:
    int dispatched() override { return 20; }
  };
  int main() { Base* b = new Derived(); return b->fixed() + b->dispatched(); }"

#eval (parseProgram staticDyn).map run
```
```leanOutput staticDyn
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

```tree
m ↦ τ m(…) { c } o método m mais próximo de S na cadeia, ou mais próximo de T quando esse método é virtual
```

* $`S` a classe estática, escrita na árvore pelo verificador. $`T` a etiqueta, lida do objeto em σ.

# §19.3 Sem esconder métodos

```lean (name := hide)
def hide : String :=
  "class Base { public: int f() { return 1; } };
  class Derived : public Base { public: int f() { return 2; } };
  int main() { return 0; }"

#eval (parseProgram hide).map check
```
```leanOutput hide
Except.ok (Except.error (CoreCpp.TypeError.redefinesNonVirtual "Derived" "f"))
```

* Uma classe derivada redefine só um método `virtual`, e o marca com `override`.

* Para um método não virtual a declaração mais próxima de $`S` e de $`T` é a *mesma*. O despacho estático e o dinâmico concordam.

* Em C++ `b->f()` e `d->f()` sobre o mesmo objeto podem rodar métodos diferentes. Em Core C++ não.

# §19.4 Destrutores e delete

```tree
ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]    S a classe estática de e
S = T ou a cadeia de S tem destrutor virtual
os destrutores da cadeia de T rodam de T até a raiz, cada um com this ↦ ℓ, dando σ₁
──────────────────────────────────────────────────────────────────────────────── (Delete)
ρ, σ ⊢ delete e ⇒ normal, ρ, σ₁ ∖ {ℓ, ℓ₁, …, ℓₙ}
```

```lean (name := dtors)
def dtors : String :=
  "class Record { public: int n; };
  class Base {
  public:
    Record* r;
    virtual ~Base() { r->n = r->n + 1; }
  };
  class Derived : public Base {
  public:
    ~Derived() { r->n = r->n + 10; }
  };
  int main() {
    Record* rec = new Record();
    Derived* d = new Derived();
    d->r = rec;
    Base* b = d;
    delete b;
    return rec->n;
  }"

#eval (parseProgram dtors).map run
```
```leanOutput dtors
Except.ok (Except.ok (CoreCpp.Val.int 11))
```

# §19.4 Três indefinidos, três erros

```lean (name := nonVirtual)
def nonVirtual : String :=
  "class Base { public: int x; ~Base() { } };
  class Derived : public Base { public: int y; };
  int main() { Base* b = new Derived(); delete b; return 0; }"

#eval (parseProgram nonVirtual).map run
```
```leanOutput nonVirtual
Except.ok (Except.error (CoreCpp.Error.deleteWithoutVirtualDtor "Base" "Derived"))
```

```lean (name := twice)
def twice : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; delete c; return 0; }"

#eval (parseProgram twice).map run
```
```leanOutput twice
Except.ok (Except.error (CoreCpp.Error.doubleDelete 1))
```

```lean (name := dangling)
def dangling : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; return c->v; }"

#eval (parseProgram dangling).map run
```
```leanOutput dangling
Except.ok (Except.error (CoreCpp.Error.danglingLocation 1))
```

# §19.4 Posse

* O destrutor *não* libera os objetos apontados pelos campos.

* Uma classe que os possui escreve `delete` nos seus ponteiros no destrutor. A posse é ensinada, não verificada.

* Um ponteiro pendente pode existir. Todo uso dele é `erro`.

* `delete nullptr` não faz nada. `delete` de um vetor libera os elementos e o registro.

# Resumo

* A *herança* estende uma classe. Um objeto tem os campos de toda a cadeia, a base raiz primeiro.

* A *subsunção*, $`D* ≈ B*`, é a única conversão entre tipos de classe.

* O *despacho* pela etiqueta para métodos `virtual`, pela classe estática nos demais, e os dois concordam porque nenhum método esconde outro.

* O *delete* roda os destrutores da etiqueta para cima e retira o objeto de σ.

* `delete` duplo, acesso após `delete` e `delete` por base sem destrutor virtual são `erro`.

Exercícios: veja as [notas de aula](../pt/Aula-19___-Heran___a-e-Despacho/).

```lean -show
end Slides19
```
