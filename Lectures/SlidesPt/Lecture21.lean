/-
Slides da Aula 21. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Sobrecarga" =>

Um nome, várias declarações, e os tipos dos argumentos escolhem

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-21___-Sobrecarga/)

```lean -show
namespace Slides21
open CoreCpp
```

# §21.1 Um nome, várias declarações

* Um nome designa um *conjunto de sobrecarga*, e uma chamada escolhe um membro dele pelos tipos dos argumentos.

* A escolha é feita em Γ, pelo verificador de tipos, e o programa que corre tem uma chamada a uma função.

* A sobrecarga *não custa nada em tempo de execução*.

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

# §21.2 A regra que seleciona um candidato

```tree
A = os candidatos de cand(f, k) que aceitam e₁, …, eₖ
A tem um elemento cujos parâmetros são exatamente os tipos dos argumentos, ou A é unitário
────────────────────────────────────────────────────────────────────────────── (T-Overload)
a chamada de f seleciona esse candidato
```

* *Aceitar* quer dizer que cada argumento por valor é aceitável no tipo do seu parâmetro, e cada argumento de parâmetro por referência denota uma posição desse tipo.

* A vazio, o erro do único candidato daquela aridade. A unitário, esse. Dois ou mais, vence o *exato*.

* Nenhum exato, a chamada é *ambígua*. Core C++ não ordena sequências de conversão.

# §21.2 Ambiguidade por subsunção

::::cols
:::col
{lbl}[Ambígua em Core C++]

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
:::
:::col
{lbl}[Exata, e aceita]

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
:::
::::

* C++ aceita a da esquerda e executa `f(B*)`, por uma página de regras de ordenação.

# §21.3 Quando duas declarações podem dividir um nome

```tree
aridades diferentes, ou ∃ i. pᵢ ≠ qᵢ e nem pᵢ nem qᵢ é std::function
──────────────────────────────────────────────────────────────────── (Distinguishable)
as duas declarações são sobrecargas
```

* Um lambda *não tem tipo próprio*, ele é conferido com o `std::function` esperado.

* Escolher um candidato exigiria o tipo do lambda, e dar tipo ao lambda exigiria o candidato.

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

# §21.4 Métodos sobrecarregam como funções

* O conjunto de sobrecarga de um nome de método é o conjunto ao longo da *cadeia*, um por assinatura.

* Mesma assinatura de um método da base, é *redefinição*, e exige `virtual` e `override`.

* Assinatura diferente, é *outra sobrecarga*, e não exige nada.

* C++ *esconde* todo `m` da base atrás de um `m` da derivada. O subconjunto toma a união da cadeia.

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

# §21.5 Operadores são membros

```tree
Γ ⊢ e₁ : C    C tem operator⊕ visível de Γ    Γ ⊢ e₁.operator⊕(e₂) : τ
──────────────────────────────────────────────────────────────────── (T-OpBin)
Γ ⊢ e₁ ⊕ e₂ : τ
```

* O *operando esquerdo decide*, então `1 + 2` mantém o seu significado e nenhuma classe o muda.

* O parâmetro é `Point& o`, porque um objeto nunca é copiado. O resultado é `Point*`, pela mesma razão.

* Aritméticos, comparações e indexação. Não `&&` e `||`, que têm curto‑circuito.

# §21.5 A forma infixa é uma chamada de método

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

* O verificador de tipos *reescreve* a forma infixa na chamada do membro. Visibilidade, resolução e despacho se aplicam como sempre.

# Resumo

* Um nome designa um *conjunto de sobrecarga*, e os tipos dos argumentos selecionam um candidato, em Γ, sem custo de execução.

* *T-Overload*. Os candidatos que aceitam, depois o exato, ou um único, ou ambiguidade.

* Duas declarações de um nome são *distinguíveis* por aridade ou por um parâmetro que não é `std::function`.

* Métodos sobrecarregam ao longo da *cadeia*, e assinatura diferente é sobrecarga, não redefinição.

* Um operador sobre um objeto é uma *chamada de membro*, que o verificador escreve, e a derivação mostra `MethodCall`.

Exercícios: veja as [notas de aula](../pt/Aula-21___-Sobrecarga/).

```lean -show
end Slides21
```
