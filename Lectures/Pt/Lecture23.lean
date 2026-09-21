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

#doc (Manual) "Aula 23: Subtipagem" =>

%%%
tag := "aula-23"
%%%

```lean -show
namespace Lecture23
open CoreCpp
```

A herança apareceu na {secref}[aula-19] como maneira de compartilhar os membros de uma classe, e trouxe consigo uma conversão, um ponteiro para classe derivada onde se espera um ponteiro para a base. Esta aula toma essa conversão pelo que ela é, a regra da *subtipagem*, e faz as perguntas que a regra levanta. Onde ela vale, quanto custa em tempo de execução, como ela convive com o polimorfismo paramétrico da {secref}[aula-22], e por que os dois se recusam a compor.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-23.pt.html).*

# Subsunção

%%%
tag := "subsuncao-regra"
%%%

Um tipo τ é *subtipo* de um tipo τ' quando uma expressão de tipo τ pode estar onde se espera uma de tipo τ'. Em Core C++ a relação vale entre ponteiros para classes de uma cadeia, e a regra que a enuncia chama‑se subsunção.

```
Γ ⊢ e : D*    D deriva de B
─────────────────────────────── (T-Sub)
Γ ⊢ e : B*
```

A regra se lê do específico para o geral. Quem tem um ponteiro para um `Square` tem um ponteiro para uma `Shape`, porque todo `Square` é uma `Shape`. A recíproca falha, e o verificador de tipos o diz.

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

A subsunção não é um juízo à parte. Ela vive dentro da relação τ ≈ τ' que as unidades anteriores usaram em declarações, atribuições, argumentos, resultados, comparações e nos ramos de um condicional, então vale em todas de uma vez. A {numref}[tbl-subsumption] lista as posições.

:::table +header
*
  * Posição
  * Regra
  * Exemplo com `D` derivada de `B`
*
  * declaração
  * T-Decl
  * `B* b = new D();`
*
  * atribuição
  * T-Assign
  * `b = d;`
*
  * argumento
  * T-Call
  * `f(d)` com `f(B* x)`
*
  * resultado
  * T-Ret
  * `return d;` em função de resultado `B*`
*
  * comparação
  * T-Eq
  * `b == d`
*
  * ramos
  * T-Cond
  * `c ? b : d`
:::

{tabcap "tbl-subsumption"}[As posições em que a subsunção vale, todas pela relação τ ≈ τ'.]

Em tempo de execução a conversão não faz nada. Um valor de ponteiro é uma posição, e a posição de um `Square` é a posição de um `Square` quer a expressão que a nomeia tenha tipo `Square*` quer tenha tipo `Shape*`. O objeto na memória guarda a sua etiqueta de classe, e é por isso que o despacho da {secref}[aula-19] encontra o método da derivada por um ponteiro para a base. A subsunção é um enunciado sobre tipos e não custa nada em tempo de execução, exatamente como a instanciação, e pela mesma razão, ela acontece em Γ.

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

A função `sum` conhece só `Shape`, e alcança a `area` de `Square` pela etiqueta. Uma função que serve a todo subtipo de um tipo sem os conhecer é o ganho prático da subtipagem, e é o que a literatura chama de *polimorfismo de inclusão*.{margin}[L. Cardelli e P. Wegner, *On Understanding Types, Data Abstraction, and Polymorphism*, ACM Computing Surveys 17(4), 1985, pp. 471 a 523.]

# Dois Tipos de Polimorfismo

%%%
tag := "dois-tipos"
%%%

O curso já encontrou três maneiras pelas quais um trecho de programa serve a vários tipos, e elas diferem no que varia e em quando a escolha é feita. A {numref}[tbl-polymorphism] as põe lado a lado.

:::table +header
*
  * Tipo
  * O que varia
  * Escolhido
  * Em Core C++
*
  * sobrecarga
  * a declaração que corre
  * em tempo de compilação, pelos tipos dos argumentos
  * um conjunto de sobrecarga em Γ
*
  * paramétrico
  * o tipo a que a declaração serve
  * em tempo de compilação, pela instanciação
  * um template de classe expandido por substituição
*
  * inclusão
  * o método que corre
  * em tempo de execução, pela etiqueta de classe
  * um método `virtual` alcançado por ponteiro para a base
:::

{tabcap "tbl-polymorphism"}[Três tipos de polimorfismo, e onde cada um decide.]

Os três respondem a perguntas diferentes. A sobrecarga dá um nome a operações que fazem coisas análogas a tipos sem relação, e os corpos nada têm em comum. O polimorfismo paramétrico dá um corpo a uma família de tipos, e o corpo não olha para o tipo. O polimorfismo de inclusão dá uma interface a uma família de classes, e cada classe traz o seu corpo, escolhido enquanto o programa corre.

Só o terceiro custa algo em tempo de execução, a indireção do despacho, e só o terceiro escolhe um comportamento que depende de um valor calculado enquanto o programa corre.

# Onde os Dois Não Compõem

%%%
tag := "variancia"
%%%

Uma pergunta natural decorre das duas tabelas. Se `Square*` é subtipo de `Shape*`, será `Stack<Square*>` subtipo de `Stack<Shape*>`. A resposta em Core C++, como em C++ e em Java, é não. Duas instanciações de um template são duas classes sem relação, e o verificador de tipos as trata como trata `Point` e `Account`.

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

A recusa não é limitação da implementação, ela protege o programa. Suponha que a conversão fosse permitida, de modo que `d` e `c` nomeassem um objeto de classe `Box<Square*>`. O tipo de `d` diz que `d->store(x)` aceita qualquer `Shape*`, então um programa poderia guardar uma `Shape` que não é `Square` em uma caixa cujo `get` promete um `Square*`, e o `c->get()->mark` seguinte leria um campo de um objeto que não o tem. A memória teria um objeto cuja etiqueta contradiz o tipo da expressão que o alcança, que é exatamente o que um sistema de tipos existe para impedir.

O enunciado geral pertence à teoria da subtipagem. Um parâmetro que aparece só em resultados pode variar com a relação de subtipo, *covariância*, um que aparece só em parâmetros precisa variar contra ela, *contravariância*, e um que aparece nos dois, como `T` em `Box`, não pode variar, *invariância*. C++ e Core C++ fazem toda instanciação invariante, que é a escolha segura e dispensa analisar onde o parâmetro ocorre. Java permite ao programador pedir variância no uso, com os curingas `? extends` e `? super`, e Scala e Kotlin a permitem na declaração.{margin}[A. Igarashi e M. Viroli, *On Variance-Based Subtyping for Parametric Types*, ECOOP 2002, LNCS 2374, Springer, pp. 441 a 469.]

Um lugar de C++ admite covariância, o tipo de resultado de um método redefinido, em que um `Shape* clona()` pode ser redefinido como `Square* clona()`. Core C++ exige assinatura igual na redefinição, então deixa esse caso de fora, e um programa do subconjunto escreve o tipo de resultado da base nos dois.

# Exercícios

%%%
tag := "exercicios-23"
%%%

{exercise "exr-sub-positions"}[] Para cada linha da {numref}[tbl-subsumption], escreva um programa pequeno do subconjunto em que a subsunção é o que faz a linha ser bem tipada, e confira cada um com o verificador de tipos.

{exercise "exr-sub-runtime"}[] Imprima a derivação do programa da {secref}[subsuncao-regra] e aponte o passo em que a conversão de `Square*` para `Shape*` acontece. Explique a resposta.

{exercise "exr-sub-array"}[] Java aceita `Square[]` onde se espera `Shape[]`, e verifica a cada escrita se o valor cabe no arranjo de fato, lançando exceção quando não cabe. Diga qual das duas decisões, a de Java e a de Core C++, você tomaria para o subconjunto, e o que a outra custaria nas regras.

{exercise "exr-variance-counterexample"}[] Escreva, em comentários sobre um programa do subconjunto, a sequência de chamadas que corromperia a memória se `Box<Square*>` fosse subtipo de `Box<Shape*>`. Diga que regra teria de mudar para permiti‑lo.

{exercise "exr-variance-readonly"}[] Dê um template cujo parâmetro aparece só em resultados, e argumente em duas frases por que a conversão seria inofensiva para ele.

{exercise "exr-covariant-result"}[] Tente redefinir um método com um tipo de resultado mais derivado, rode o verificador de tipos, e diga o que teria de ser acrescentado a `T-Class` para aceitá‑lo.

```lean -show
end Lecture23
```
