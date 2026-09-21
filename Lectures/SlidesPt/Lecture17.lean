/-
Slides da Aula 17. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Tipos Abstratos de Dados" =>

Assinatura e representação, a visibilidade como regra de tipos, a tabela de classes

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-17___-Tipos-Abstratos-de-Dados/)

{cite}[B. Liskov e S. Zilles, *Programming with Abstract Data Types*, SIGPLAN Notices 9(4), 1974.]

```lean -show
namespace Slides17
open CoreCpp
```

# §17.1 Assinatura e representação

* Uma pilha é conhecida por quatro operações. Criar, empilhar, desempilhar, vazia.

* As operações são a *assinatura*. O vetor e o contador são a *representação*.

* Quem usa o tipo depende só da assinatura, então a representação pode mudar sem tocar nos clientes.

* A assinatura é um *contrato*, a representação uma decisão privada.

{cite}[D. L. Parnas, *On the Criteria To Be Used in Decomposing Systems into Modules*, CACM 15(12), 1972.]

# §17.1 Uma pilha em Core C++

```lean (name := stack)
def stack : String :=
  "class Stack {
  private:
    std::vector<int>* items;
    int top;
  public:
    Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
    void push(int x) { (*items)[top] = x; top = top + 1; }
    int pop() { top = top - 1; return (*items)[top]; }
    bool empty() { return top == 0; }
  };
  int main() {
    Stack* p = new Stack(8);
    p->push(1);
    p->push(41);
    return p->pop() + p->pop();
  }"

#eval (parseProgram stack).map run
```
```leanOutput stack
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

# §17.2 A visibilidade é uma regra de tipos

```lean (name := peek)
def peek : String :=
  "class Stack {
  private:
    std::vector<int>* items;
    int top;
  public:
    Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
  };
  int main() { Stack* p = new Stack(8); return p->top; }"

#eval (parseProgram peek).map check
```
```leanOutput peek
Except.ok (Except.error (CoreCpp.TypeError.privateMember "Stack" "top"))
```

* O contrato é imposto *antes de o programa rodar*.

# §17.2 A regra Visible

```tree
C tem τ f declarado em K    f público ou Γ(this) = K*
──────────────────────────────────────────────────── (Visible)
```

* Dentro de um corpo de membro Γ liga `this` a $`C*`. A *classe corrente* é a classe de `this`.

* Fora de toda classe não há `this`, então só membros públicos são visíveis.

* Uma classe derivada não vê os membros privados da base. A mesma regra de C++.

* Core C++ mantém só `public` e `private`. Sem `protected`, `friend` ou `static`.

# §17.3 A tabela de classes

:::table +header
*
  * Pergunta
  * Resposta
*
  * cadeia de uma classe
  * a classe, a sua base, a base da base, até a raiz
*
  * campos de um objeto
  * todo campo da cadeia, a base raiz primeiro
*
  * método de uma classe
  * a declaração mais próxima com esse nome na cadeia
*
  * $`D` deriva de $`B`
  * $`B` está na cadeia de $`D`
*
  * destrutor virtual
  * alguma classe da cadeia declara um
:::

* O verificador de tipos, `new`, `delete` e o despacho consultam a mesma tabela.

# §17.4 Uma classe bem formada

```tree
B existe e a cadeia de C não tem ciclo
campos com valores, bem formados, novos na cadeia
membros com nomes distintos
cada método redefinido é virtual na base, leva override, mesma assinatura
o construtor de B, se existe, não tem parâmetros
[this ↦ C*, x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'   para todo corpo de membro
──────────────────────────────────────────────────────────────── (T-Class)
⊢ class C : public B { … }
```

* Os corpos são verificados sob `this ↦ C*` e os parâmetros. Construtores e destrutores devolvem `void`.

* Sem listas de inicialização, então o construtor da base não tem parâmetros.

# §17.5 Invariantes de representação

* Uma propriedade que toda operação preserva. Para a pilha, `top` fica nos limites e os valores abaixo dele são os empilhados e não desempilhados.

* A visibilidade torna o invariante *demonstrável*. Só os métodos escrevem os campos, então basta verificar cada método.

* Um cliente que empilha nove valores em uma pilha de oito quebra o contrato. Em C++ a escrita é indefinida. Em Core C++ é `erro`, por `LocIndex`.

* Uma pilha que confere os limites mantém o invariante por conta própria.

# Resumo

* Um *tipo abstrato de dados* é uma assinatura sobre uma representação escondida. Em Core C++, uma `class` com seções `public` e `private`.

* A *visibilidade* é uma regra de tipos. Um membro privado de $`K` é visível só quando `this` tem classe $`K`.

* A *tabela de classes* responde a toda pergunta sobre cadeias, campos, métodos e destrutores.

* `T-Class` verifica a forma da classe e cada corpo de membro sob `this ↦ C*`.

* A visibilidade é o que torna um *invariante de representação* demonstrável verificando só os métodos.

Exercícios: veja as [notas de aula](../pt/Aula-17___-Tipos-Abstratos-de-Dados/).

```lean -show
end Slides17
```
