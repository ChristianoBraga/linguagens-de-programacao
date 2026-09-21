/-
Slides da Aula 26. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "O Paradigma Orientado a Objetos" =>

O fragmento com o monte e a classe, encapsulamento e despacho

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-26___-O-Paradigma-Orientado-a-Objetos/)

```lean -show
namespace Slides26
open CoreCpp
```

# §26.1 O fragmento

* O fragmento imperativo *mais* a classe, métodos, construtores, destrutores, `this`, herança, `virtual`, despacho, `new`, `delete`, ponteiros, vetores, sobrecarga, templates, namespaces.

* Proíbe três construções, o *lambda*, o tipo `std::function` e a chamada por valor de função.

* As três são a mesma coisa de três lados, *a função como valor*. Este paradigma empacota comportamento em um *objeto*.

```lean (name := ooNotFn)
def comLambda : String :=
  "std::function<int()> f() {
     return [=]() -> int { return 1; };
   }
   int main() { return f()(); }"

#eval (parseProgram comLambda).map (fragment .oo)
```
```leanOutput ooNotFn
Except.ok (Except.error { frag := CoreCpp.Frag.oo, what := "function type", site := "function f" })
```

# §26.2 O que o monte custa

* *Os valores de σ deixam de ser básicos.* Objetos, vetores e ponteiros vivem lá.

* *A memória deixa de ser pilha.* `New` aloca, nada libera na saída do bloco, o `delete` pode estar em qualquer lugar ou em lugar nenhum.

* *Uma posição pendente torna‑se alcançável.* Três resultados `erro` respondem por ela, em vez de comportamento indefinido.

* *Um enunciado sobrevive.* Toda posição do monte é alcançada por um *ponteiro* ou por `this`. Não há terceiro canal, porque o fragmento não tem closure nem variável global.

# §26.3 Encapsulamento e despacho

::::cols
:::col
{lbl}[Encapsulamento]

* A representação é conhecida só dentro da classe.

* Uma regra de tipos, verificada em Γ *antes* de o programa correr.

* A classe é um tipo abstrato de dados, assinatura pública e representação privada.
:::
:::col
{lbl}[Despacho]

* O código que a chamada executa é conhecido só em execução, pela *etiqueta de classe*.

* A regra `Dispatch`, condicionada a `virtual`.

* O chamador conhece a assinatura, não o código.
:::
::::

* Os dois são restrições sobre *quem pode saber o quê*, e juntos permitem estender um programa com uma classe que o seu autor nunca viu.

# §26.3 O estudo de caso

```lean (name := caseOo)
def caseOo : String :=
  "class Adder {
   public:
     int acc;
     virtual bool accepts(int i) { return true; }
     void add(int i) { if (accepts(i)) { acc = acc + i; } }
     int total() { return acc; }
     virtual ~Adder() { }
   };
   class EvenAdder : public Adder {
   public:
     bool accepts(int i) override { return i % 2 == 0; }
   };
   int main() {
     Adder* s = new EvenAdder();
     for (int i = 1; i <= 10; i = i + 1) { s->add(i); }
     int r = s->total();
     delete s;
     return r;
   }"

#eval (parseProgram caseOo).map fun p => (fragment .oo p, run p)
```
```leanOutput caseOo
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* `add` é declarado uma vez e chama `accepts`, que a derivada redefine. Um terceiro critério é *uma classe nova e nenhuma mudança em junta*.

# §26.4 Despacho e closure

* Os dois empacotam comportamento e o levam aonde não se sabe qual é.

* O *método* viaja dentro de um objeto, com o seu estado, selecionado por uma etiqueta. O *closure* viaja sozinho, com as suas cópias, selecionado por ser aquele valor.

* O despacho põe o ponto de extensão na *hierarquia de tipos*. O closure o põe na *lista de argumentos*.

* Nenhum é melhor. Distribuem a mesma liberdade de outro modo, e Core C++ tem os dois.

# Resumo

* O fragmento orientado a objetos é o imperativo *com o monte e a classe*, e sem a função como valor.

* O monte custa a disciplina de pilha e torna alcançável uma posição pendente, respondida por três resultados `erro`.

* O que sobrevive é que toda posição do monte é alcançada por *ponteiro* ou por `this`.

* *Encapsulamento* e *despacho* são ambos regras de tipos, e ambos tratam de quem pode saber o quê.

* O ponto de extensão do paradigma é a *hierarquia de classes*.

Exercícios: veja as [notas de aula](../pt/Aula-26___-O-Paradigma-Orientado-a-Objetos/).

```lean -show
end Slides26
```
