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

#doc (Manual) "Aula 19: Herança e Despacho" =>

%%%
tag := "aula-19"
%%%

```lean -show
namespace Lecture19
open CoreCpp
```

Esta aula trata as duas construções que fazem de uma classe mais do que um tipo abstrato de dados. A *herança* permite a uma classe estender outra com campos e métodos, e o *despacho dinâmico* permite a uma chamada por um ponteiro para a base rodar o método da classe derivada do objeto. A aula escreve a subsunção como regra de tipos, o despacho como premissa da regra `MethodCall`, e o destrutor e o `delete` como o fim da vida de um objeto, com os três casos que C++17 deixa indefinidos transformados em `erro`.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-19.pt.html).*

# Herança Simples

%%%
tag := "heranca"
%%%

Uma classe `D : public B` *deriva* de `B`. Um objeto de `D` tem todo campo de `B` e depois os campos de `D`, e um método de `B` se aplica a ele a menos que `D` redefina o método. As classes `B`, `D` e toda classe que deriva de `D` formam uma *cadeia*, e a tabela de classes da {secref}[aula-17] responde a toda pergunta sobre uma classe percorrendo a sua cadeia até a raiz.

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

O programa mostra as três construções da aula de uma vez. Um `Square*` é guardado em uma variável de tipo `Shape*`, a *subsunção*. A chamada `f->area()` roda o método de `Square` embora o ponteiro tenha tipo `Shape*`, o *despacho*. O `delete f` pelo ponteiro para a base alcança o objeto porque o destrutor de `Shape` é `virtual`. As classes ficam em um `namespace`, {secref}[aula-20].

# Subsunção

%%%
tag := "subsuncao"
%%%

Um ponteiro para uma classe derivada é aceito onde quer que se espere um ponteiro para a sua base. A relação τ ≈ τ' da {secref}[aula-8], que dizia quando o tipo de um valor é aceito em um tipo esperado, ganha um caso.

```
D deriva de B
────────────────── (Subsumption)
D* ≈ B*
```

A regra se aplica em declarações, atribuições, argumentos, retornos, comparações e nos ramos de `?:`, onde quer que ≈ apareça em uma premissa. É a única conversão entre tipos de classe. A direção oposta, um `B*` onde se espera um `D*`, é erro de tipo, porque o objeto atrás de um `B*` pode ser um `B` simples, sem os campos de `D`.

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

A subsunção dá à linguagem a *subtipagem*, conceito da UD VI, na sua forma mais simples. O tipo de uma expressão, `Shape*`, pode ser um supertipo próprio do tipo do objeto que ela denota, `Square*`, e os dois podem diferir em todo ponto do programa. O verificador de tipos conhece só o primeiro, o *tipo estático*. O avaliador vê só o segundo, a *etiqueta de classe* do objeto em σ. O despacho é a regra que decide qual dos dois governa uma chamada de método.

# Despacho

%%%
tag := "despacho"
%%%

Um método marcado `virtual` é escolhido pela etiqueta de classe do receptor, a declaração mais próxima na cadeia da etiqueta, então uma chamada por um ponteiro para a base alcança a redefinição da classe derivada. Um método que não é `virtual` é escolhido pela classe estática do receptor.

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

A premissa de `MethodCall` que a {secref}[aula-18] deixou em aberto lê‑se assim, com $`S` a classe estática do receptor e $`T` a etiqueta de classe do objeto.

```
m ↦ τ m(…) { c } o método m mais próximo de S na cadeia, ou mais próximo de T quando esse método é virtual
```

A classe estática vem do verificador de tipos. Nem ρ nem σ carregam tipos, então, depois de um programa ser verificado, o verificador escreve em cada chamada de método a classe que o receptor tem em Γ, e o avaliador a lê ali. A etiqueta vem do objeto em σ.

Core C++ acrescenta uma restrição que C++ não tem. Uma classe derivada redefine um método só quando a base o declara `virtual`, e então o marca com `override`. Redefinir um método não virtual, o que em C++ *esconde* o método da base, é erro de tipo.

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

A restrição tem uma consequência agradável. Para um método não virtual, a declaração mais próxima a partir de $`S` e a mais próxima a partir de $`T` são a mesma, porque nenhuma classe entre $`T` e $`S` o redeclara. O despacho estático e o dinâmico então concordam em todo método que não é `virtual`, e um programa que esconde um método, a fonte clássica de surpresa em C++, não pode ser escrito.{fnref}[hiding]

:::footnotes

{fnAnchor "hiding"}[] Em C++ a chamada `b->f()` acima roda `Base::f`, porque `f` não é virtual e `b` tem tipo estático `Base*`, enquanto `d->f()` em um `Derived*` para o mesmo objeto roda `Derived::f`. O mesmo objeto responde à mesma mensagem de dois modos, conforme o tipo do ponteiro que o nomeia, e o compilador não emite diagnóstico. A palavra `override` de C++11 captura só o erro oposto, um método que pretendia redefinir e não redefine. Core C++ exige `override` em toda redefinição e proíbe o caso de esconder, então as duas políticas de despacho só podem diferir em métodos virtuais, onde a diferença é o objetivo.

:::

# Destrutores e delete

%%%
tag := "delete"
%%%

Um objeto criado por `new` vive em σ até o `delete` ou o fim do programa. O comando `delete e` avalia `e` para a posição de um objeto, roda os *destrutores* da sua cadeia da etiqueta até a raiz, cada um com `this` ligado ao objeto, e retira de σ o registro e as posições dos campos.

```
Γ ⊢ e : C*                    Γ ⊢ e : std::vector<τ>*
──────────────── (T-Delete)   ──────────────────────── (T-DeleteVec)
Γ ⊢ delete e ⊣ Γ              Γ ⊢ delete e ⊣ Γ

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]    S a classe estática de e
S = T ou a cadeia de S tem destrutor virtual
os destrutores da cadeia de T rodam de T até a raiz, cada um com this ↦ ℓ, dando σ₁
──────────────────────────────────────────────────────────────────────────────── (Delete)
ρ, σ ⊢ delete e ⇒ normal, ρ, σ₁ ∖ {ℓ, ℓ₁, …, ℓₙ}
```

Um destrutor é um membro `~C()` sem parâmetros e sem resultado, e uma classe tem no máximo um. A ordem, derivada primeiro e base por último, é a inversa da dos construtores. Um programa pode observá‑la por um objeto que os dois destrutores atualizam.

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

O destrutor de `Base` é `virtual`, e é isso que torna `delete b` pelo ponteiro para a base bem definido. A premissa `S = T ou a cadeia de S tem destrutor virtual` enuncia a condição de C++17. Quando a classe estática difere da etiqueta e nenhuma classe da cadeia da classe estática declara destrutor virtual, C++ deixa o comportamento indefinido, em geral rodando só o destrutor da base, e Core C++ o torna `erro`.

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

Dois outros casos são indefinidos em C++ e `erro` em Core C++, ambos pela regra de que uma posição fora de σ é `erro`. Um segundo `delete` do mesmo objeto não encontra objeto na posição.

```lean (name := twice)
def twice : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; delete c; return 0; }"

#eval (parseProgram twice).map run
```
```leanOutput twice
Except.ok (Except.error (CoreCpp.Error.doubleDelete 1))
```

Um acesso depois do `delete` não encontra posição para o campo.

```lean (name := dangling)
def dangling : String :=
  "class Box { public: int v; };
  int main() { Box* c = new Box(); delete c; return c->v; }"

#eval (parseProgram dangling).map run
```
```leanOutput dangling
Except.ok (Except.error (CoreCpp.Error.danglingLocation 1))
```

O ponteiro `c` ainda guarda ℓ1 depois do `delete`, um *ponteiro pendente*. Core C++ não o proíbe, porque proibi‑lo exigiria uma análise de todo caminho do programa, mas todo uso dele é `erro`, e não uma leitura silenciosa de memória liberada. O destrutor não libera os objetos apontados pelos campos. Uma classe que os possui escreve `delete` nos seus ponteiros no destrutor, e a posse é ensinada, não verificada, como o projeto enuncia. `delete nullptr` não faz nada, e `delete` de um vetor libera os elementos e o registro, ambos como em C++.

# A Árvore de Derivação de um delete

%%%
tag := "trace-19"
%%%

```lean (name := traceDelete)
def traceDelete : String :=
  "class Box {
  public:
    int v;
    ~Box() { v = 0; }
  };
  int main() { Box* c = new Box(); c->v = 7; delete c; return 1; }"

#eval match parseProgram traceDelete with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceDelete
    [], {} ⊢ new Box() ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}}   (New)
  [], {} ⊢ Box* c = new Box(); ⇒ normal, [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Decl)
    [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 7 ⇒ 7, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
        [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
      [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
    [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c->v ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
  [c ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c->v = 7; ⇒ normal, [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
      [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ₗ ℓ2, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
    [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
      [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 0 ⇒ 0, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
      [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
    [this ↦ ℓ1], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ v = 0; ⇒ normal, [this ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
  [c ↦ ℓ2], {ℓ0 ↦ 7, ℓ1 ↦ Box{v ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ delete c; ⇒ normal, [c ↦ ℓ2], {ℓ2 ↦ ℓ1}   (Delete)
    [c ↦ ℓ2], {ℓ2 ↦ ℓ1} ⊢ 1 ⇒ 1, {ℓ2 ↦ ℓ1}   (Lit)
  [c ↦ ℓ2], {ℓ2 ↦ ℓ1} ⊢ return 1; ⇒ ret 1, [c ↦ ℓ2], {ℓ2 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 1, {}   (Call)
```

A linha do `delete` avalia `c`, roda o corpo do destrutor sob `[this ↦ ℓ1]`, que escreve zero no campo, e conclui com uma memória em que ℓ0 e ℓ1 desapareceram. Só ℓ2, a variável `c` de `main`, permanece, e o seu conteúdo ainda é ℓ1, o ponteiro pendente. O `return` de `main` então libera ℓ2 e a memória final é vazia. Todo objeto que o programa criou foi apagado.

# Exercícios

%%%
tag := "exercicios-19"
%%%

{exercise "exr-chain-fields"}[] Escreva três classes em cadeia, cada uma com um campo, crie um objeto da mais derivada e escreva o registro que a regra `New` constrói, com a ordem dos campos.

{exercise "exr-dispatch-both"}[] Acrescente a `Derived` da {secref}[despacho] um método não virtual que não existe em `Base`, e o chame por um `Derived*` e por um `Base*`. Explique os dois desfechos pelas regras.

{exercise "exr-hiding-cpp"}[] Compile o programa de `hide` com `g++`, chame `f` por um `Base*` e por um `Derived*` para o mesmo objeto, e relate os dois resultados. Explique por que Core C++ rejeita o programa em vez disso.

{exercise "exr-dtor-order"}[] Estenda a cadeia da {secref}[delete] com uma terceira classe cujo destrutor soma 100 ao registro, e preveja o resultado antes de rodar.

{exercise "exr-ownership"}[] Escreva uma classe que possui um vetor por um campo ponteiro e o libera no destrutor. Depois retire o `delete` do destrutor e explique o que resta em σ no fim do programa, e por que Core C++ não o reporta.

{exercise "exr-undefined-three"}[] Para cada um dos três casos indefinidos de C++17 desta aula, escreva um programa de Core C++ que produz o `erro` correspondente, e o compile com `g++` para observar o que o programa compilado faz.

```lean -show
end Lecture19
```
