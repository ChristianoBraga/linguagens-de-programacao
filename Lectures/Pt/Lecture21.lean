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

#doc (Manual) "Aula 21: Sobrecarga" =>

%%%
tag := "aula-21"
%%%

```lean -show
namespace Lecture21
open CoreCpp
```

Esta aula abre a UD VI com a primeira forma de polimorfismo que uma linguagem oferece, a *sobrecarga*, em que um nome designa várias declarações e os tipos dos argumentos escolhem entre elas. A aula dá a regra que seleciona um candidato, diz quando duas declarações de um nome podem conviver, e termina com os operadores, que em C++ são membros com um nome próprio. A escolha acontece em Γ, antes de o programa correr, então a sobrecarga não custa nada em tempo de execução.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-21.pt.html).*

# Um Nome, Várias Declarações

%%%
tag := "conjunto-sobrecarga"
%%%

Um programa pode declarar várias funções com um nome, desde que elas recebam argumentos diferentes. O nome designa então um *conjunto de sobrecarga*, e uma chamada escolhe um membro do conjunto pelos tipos dos seus argumentos. A escolha é do verificador de tipos, e o programa que corre tem uma chamada a uma função, como se o programador tivesse escrito três nomes distintos.

```lean (name := overload)
def overload : String :=
  "int twice(int n) { return 2 * n; }
  bool twice(bool b) { return b; }
  int twice(int a, int b) { return 2 * (a + b); }
  int main() {
    int x = twice(21);
    int y = twice(1, 1);
    return twice(false) ? 0 : x + y;
  }"

#eval (parseProgram overload).map run
```
```leanOutput overload
Except.ok (Except.ok (CoreCpp.Val.int 46))
```

As três declarações de `twice` diferem no número de argumentos, no primeiro caso, e no tipo do argumento, no segundo. Cada chamada de `main` alcança uma delas. Nada nos valores distingue as chamadas em tempo de execução, e o interpretador sabe em que função entrar porque o verificador de tipos escreve na árvore a *assinatura* da declaração escolhida.

A utilidade é de nomeação. Sem sobrecarga, uma biblioteca que imprime um `int`, um `bool` e um ponteiro oferece três nomes, `imprimeInt`, `imprimeBool`, `imprimePonteiro`, e o leitor precisa lembrar qual escrever. Com sobrecarga ela oferece `imprime`, e o argumento decide. Em troca, o leitor de uma chamada precisa conhecer os tipos dos argumentos para saber qual declaração corre, e por isso uma linguagem que sobrecarrega deve manter os candidatos poucos e distintos.

# A Regra que Seleciona um Candidato

%%%
tag := "resolucao"
%%%

Seja `cand(f, k)` o conjunto das declarações de `f` com `k` parâmetros. Um candidato *aceita* os argumentos quando cada argumento por valor é aceitável no tipo do seu parâmetro, o juízo Γ ⊢ e ◁ τ da {secref}[aula-15], e cada argumento de parâmetro por referência denota uma posição do tipo do parâmetro. Os candidatos que aceitam formam o conjunto A, e a regra escolhe em A.

```
A = os candidatos de cand(f, k) que aceitam e₁, …, eₖ
A tem um elemento cujos parâmetros são exatamente os tipos dos argumentos, ou A é unitário
────────────────────────────────────────────────────────────────────────────── (T-Overload)
a chamada de f seleciona esse candidato
```

Três casos decorrem da regra. Com A vazio a chamada falha, e a mensagem é a do único candidato daquela aridade quando existe um, então um programa com um só `twice` recebe a mensagem comum de tipo e não uma queixa vaga sobre sobrecargas. Com A unitário a escolha é esse candidato. Com dois ou mais em A vence o exato, e se nenhum é exato a chamada é *ambígua* e o programa é recusado.

Um candidato exato é aquele cujos tipos de parâmetro são os tipos dos argumentos, sem conversão alguma. As conversões que podem ficar entre um argumento e um parâmetro são as três do subconjunto, `nullptr` para um ponteiro, um lambda para um `std::function`, e a subsunção, um ponteiro para classe derivada onde se espera um ponteiro para a base. É a última que produz ambiguidade.

```lean (name := ambiguous)
def ambiguous : String :=
  "class A { public: int a; };
  class B : public A { public: int b; };
  class C : public B { public: int c; };
  int f(A* x) { return 1; }
  int f(B* x) { return 2; }
  int main() { C* z = new C(); return f(z); }"

#eval (parseProgram ambiguous).map check
```
```leanOutput ambiguous
Except.ok (Except.error (CoreCpp.TypeError.ambiguousCall "f"))
```

Um `C*` alcança `f(A*)` e `f(B*)` por subsunção, e nenhum é exato, então Core C++ recusa a chamada. C++ a aceita e executa `f(B*)`, porque ordena as sequências de conversão e uma conversão para a base mais próxima é melhor do que uma para a mais distante.{margin}[ISO/IEC 14882:2017, cláusula 16.3.3, *Best viable function*.] A ordenação é uma página de regras, e o subconjunto a troca por uma linha e um erro claro. Um programa que precisa do comportamento de C++ escreve o cast, ou dá nomes diferentes às duas funções.

Quando um candidato é exato a escolha é ele, e nenhuma ambiguidade aparece.

```lean (name := exact)
def exact : String :=
  "class A { public: int a; };
  class B : public A { public: int b; };
  int f(A* x) { return 1; }
  int f(B* x) { return 2; }
  int main() { B* z = new B(); return f(z); }"

#eval (parseProgram exact).map run
```
```leanOutput exact
Except.ok (Except.ok (CoreCpp.Val.int 2))
```

# Quando Duas Declarações Podem Dividir um Nome

%%%
tag := "distinguiveis"
%%%

Nem todo par de declarações pode dividir um nome. Duas delas precisam ser *distinguíveis*, isto é, diferem no número de parâmetros, ou em alguma posição em que os dois tipos diferem e nenhum é um `std::function`.

```
aridades diferentes, ou ∃ i. pᵢ ≠ qᵢ e nem pᵢ nem qᵢ é std::function
──────────────────────────────────────────────────────────────────── (Distinguishable)
as duas declarações são sobrecargas
```

A condição sobre `std::function` merece a sua própria razão. Um lambda não tem tipo próprio em Core C++, como a {secref}[aula-15] mostrou. Ele é conferido com o tipo `std::function` esperado na sua posição, o que exige conhecer o tipo esperado *antes* de olhar o lambda. Se dois candidatos diferissem só em um parâmetro `std::function`, escolher entre eles exigiria o tipo do lambda, e dar tipo ao lambda exigiria escolher um candidato.

```lean (name := indistinguishable)
def indistinguishable : String :=
  "int g(std::function<int(int)> h) { return h(1); }
  int g(std::function<bool(bool)> h) { return 0; }
  int main() { return 0; }"

#eval (parseProgram indistinguishable).map check
```
```leanOutput indistinguishable
Except.ok (Except.error (CoreCpp.TypeError.indistinguishable "g"))
```

As duas declarações são recusadas onde estão, na declaração, e não em alguma chamada posterior. É o lugar útil para a mensagem, porque o autor da biblioteca sabe do problema sem esperar que um cliente escreva uma chamada ambígua. C++ aceita as duas, porque lá um lambda tem um tipo de closure próprio que distingue as chamadas, ao preço de toda a maquinaria dos tipos de closure.{fnref}[closuretype]

Duas declarações de mesmo nome e mesma assinatura não são sobrecargas, são uma declaração escrita duas vezes, e o verificador de tipos relata declaração repetida.

:::footnotes

{fnAnchor "closuretype"}[] Em C++ cada expressão lambda tem um tipo de classe anônimo distinto, e `std::function<int(int)>` é uma classe comum que guarda qualquer chamável da forma certa. Uma chamada `g([=](int x) -> int { return x; })` tem então um argumento de tipo de closure, e os candidatos são ordenados pela conversão desse tipo para cada `std::function`. Core C++ nunca forma o tipo de closure, que é a decisão da UD IV, então a informação que ordenaria os candidatos não existe, e o subconjunto proíbe o par em vez de adivinhar.

:::

# Métodos Sobrecarregam como Funções

%%%
tag := "metodos-sobrecarga"
%%%

O conjunto de sobrecarga de um nome de método é o conjunto dos métodos com esse nome ao longo da cadeia da classe, um por assinatura. Um método de uma classe derivada com a assinatura de um método da base o redefine, o que é a redefinição da {secref}[aula-19] e exige `virtual` e `override`. Um método de uma derivada com o mesmo nome e assinatura *diferente* é outra sobrecarga, e não exige nada.

```lean (name := methodOverload)
def methodOverload : String :=
  "class Account {
  private:
    int balance;
  public:
    Account(int s) { this->balance = s; }
    int deposit(int v) { balance = balance + v; return balance; }
    int deposit(int v, int rate) { return deposit(v - rate); }
    int value() { return balance; }
  };
  int main() {
    Account* c = new Account(100);
    c->deposit(50);
    c->deposit(20, 5);
    return c->value();
  }"

#eval (parseProgram methodOverload).map run
```
```leanOutput methodOverload
Except.ok (Except.ok (CoreCpp.Val.int 165))
```

A chamada `deposit(v - rate)` dentro do método de dois argumentos é um nome não qualificado, que a {secref}[aula-18] leu como `this->deposit(...)`, e o conjunto de sobrecarga de `this` a resolve para o método de um argumento. A recursão que um leitor poderia temer não acontece, porque as aridades diferem.

C++ tem aqui uma regra que Core C++ deixa de fora. Um membro de nome `m` em uma classe derivada *esconde* todos os `m` da base, então uma sobrecarga declarada na base fica inalcançável por um objeto da derivada, a menos que a derivada escreva `using Base::m`. O subconjunto toma a união ao longo da cadeia, o que não perde programa algum e poupa uma regra.

# Operadores São Membros

%%%
tag := "operadores"
%%%

Um operador em C++ é uma função com um nome especial, e uma classe pode lhe dar significado para os seus objetos. Em Core C++ um operador é um *membro*, declarado com a palavra reservada `operator` seguida do operador, e recebe o operando direito como único parâmetro. O receptor é o operando esquerdo.

```lean (name := operatorPlus)
def operatorPlus : String :=
  "class Point {
  public:
    int x;
    int y;
    Point* operator+(Point& o) {
      Point* r = new Point();
      r->x = x + o.x;
      r->y = y + o.y;
      return r;
    }
  };
  int main() {
    Point* a = new Point();
    a->x = 1; a->y = 4;
    Point* b = new Point();
    b->x = 2; b->y = 3;
    Point* c = *a + *b;
    return c->x + c->y;
  }"

#eval (parseProgram operatorPlus).map run
```
```leanOutput operatorPlus
Except.ok (Except.ok (CoreCpp.Val.int 10))
```

Dois detalhes da declaração decorrem de decisões de unidades anteriores. O parâmetro é `Point& o` e não `Ponto o`, porque um objeto nunca é copiado nem guardado em variável, então a única maneira de passar um é ligar a sua posição, o que um parâmetro por referência faz. O resultado é `Point*` e não `Point`, pela mesma razão, então o operador cria o resultado com `new` e devolve o ponteiro.

A regra de tipos diz que um operador infixo cujo operando esquerdo é um objeto é a chamada do membro.

```
Γ ⊢ e₁ : C    C tem operator⊕ visível de Γ    Γ ⊢ e₁.operator⊕(e₂) : τ
──────────────────────────────────────────────────────────────────── (T-OpBin)
Γ ⊢ e₁ ⊕ e₂ : τ
```

O operando esquerdo decide. Um operador sobre dois `int` mantém o significado da {secref}[aula-8], porque o operando esquerdo é um `int` e não um objeto, e nenhuma classe muda o significado de `1 + 2`. Os operadores que uma classe pode sobrecarregar são os aritméticos, as comparações e a indexação. Os lógicos `&&` e `||` ficam de fora, porque têm curto‑circuito e uma chamada de membro avaliaria os dois operandos, o que mudaria o significado do operador em vez de o estender.

A reescrita não é figura de linguagem. O verificador de tipos substitui a forma infixa pela chamada de método, e a derivação do programa mostra a regra `MethodCall` onde o fonte mostra um `+`.

```lean (name := operatorTrace)
def small : String :=
  "class P {
  public:
    int x;
    P* operator+(P& o) {
      P* r = new P();
      r->x = x + o.x;
      return r;
    }
  };
  int main() {
    P* a = new P();
    a->x = 21;
    P* c = *a + *a;
    return c->x;
  }"

#eval match parseProgram small with
  | .ok p =>
    IO.println (String.intercalate "\n"
      ((renderTrace (runWith true p).2).splitOn "\n" |>.filter
        fun l => l.endsWith "(MethodCall)"))
  | .error e => IO.println e
```
```leanOutput operatorTrace
    [a ↦ ℓ2], {ℓ0 ↦ 21, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ *a + *a ⇒ ℓ4, {ℓ0 ↦ 21, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1, ℓ3 ↦ 42, ℓ4 ↦ P{x ↦ ℓ3}}   (MethodCall)
```

Feita a reescrita, a chamada é uma chamada de método comum. A visibilidade se aplica, então um operador declarado `private` é inalcançável de fora da classe. A resolução de sobrecarga se aplica, então uma classe pode declarar `operator+` duas vezes com tipos de parâmetro diferentes. O despacho se aplica, então um operador declarado `virtual` na base e redefinido na derivada é escolhido pela etiqueta de classe do operando esquerdo.

# Exercícios

%%%
tag := "exercicios-21"
%%%

{exercise "exr-overload-print"}[] Escreva três declarações de `imprime`, para `int`, para `bool` e para um ponteiro para uma classe à sua escolha, cada uma devolvendo um valor distinto, e um `main` que chama as três. Diga para cada chamada qual candidato a regra seleciona e por quê.

{exercise "exr-overload-ambiguity"}[] Dê um programa com duas sobrecargas e uma chamada que é ambígua em Core C++ e aceita por `g++`. Compile com `g++` e execute, e explique, pela cláusula 16.3.3 da norma, qual candidato C++ escolhe.

{exercise "exr-overload-exact"}[] Mude o programa do exercício anterior em uma linha para que a chamada passe a ser exata, e explique a mudança em termos do conjunto A da regra.

{exercise "exr-overload-function"}[] Tente declarar duas funções que diferem só em um parâmetro `std::function`, rode o verificador de tipos e explique a mensagem. Depois reescreva o par de modo que as duas permaneçam e as chamadas não mudem, acrescentando um parâmetro a uma delas.

{exercise "exr-operator-compare"}[] Dê à classe `Pair` um membro `operator<` que compara pelo primeiro campo, e um `main` que o usa na condição de um `if`. Imprima a derivação e encontre a linha em que a comparação virou chamada de método.

{exercise "exr-operator-short-circuit"}[] Explique, com um exemplo que tenha efeito de um dos lados, o que mudaria no significado de um programa se Core C++ permitisse a uma classe sobrecarregar `&&`.

```lean -show
end Lecture21
```
