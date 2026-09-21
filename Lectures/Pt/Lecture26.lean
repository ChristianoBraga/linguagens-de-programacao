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

#doc (Manual) "Aula 26: O Paradigma Orientado a Objetos" =>

%%%
tag := "aula-26"
%%%

```lean -show
namespace Lecture26
open CoreCpp
```

O fragmento orientado a objetos é o imperativo com o monte e a classe. A aula dá o fragmento, diz o que o monte custa nos enunciados da {secref}[aula-25] e o que o encapsulamento e o despacho compram em troca, e modela o estudo de caso da unidade com classes. A leitura que ela propõe é que um programa desse paradigma é um conjunto de objetos que guardam estado e respondem a mensagens, e que os dois princípios organizadores, o encapsulamento e o despacho, tratam ambos de *quem pode saber o quê*.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-26.pt.html).*

# O Fragmento

%%%
tag := "fragmento-oo"
%%%

O fragmento orientado a objetos admite tudo o que o imperativo admite, e acrescenta a classe com os seus campos, métodos, construtor e destrutor, `this`, herança simples, `virtual`, `override`, despacho, subsunção, `new`, `delete`, ponteiros, vetores, sobrecarga, membros operadores, templates de classe e namespaces. Proíbe três construções, o lambda, o tipo `std::function` e a chamada por valor de função.

As três proibidas são a mesma construção vista de três lados, a função como valor. Uma linguagem desse paradigma empacota comportamento em um objeto, não em um valor de tipo função, então o fragmento pede que um programa diga com um método `virtual` o que de outro modo diria com um lambda. É esse o sentido da restrição, e a {secref}[despacho-closure] volta a ela.

```lean (name := ooCheck)
def conta : String :=
  "class Conta {
   public:
     int saldo;
     virtual int taxa() { return 2; }
     void deposita(int v) { saldo = saldo + v; }
     virtual ~Conta() { }
   };
   class Poupanca : public Conta { public: int taxa() override { return 0; } };
   int main() {
     Conta* c = new Conta(); c->deposita(10);
     Conta* p = new Poupanca(); p->deposita(10);
     int r = c->taxa() + p->taxa() + c->saldo;
     delete c; delete p; return r;
   }"

#eval (parseProgram conta).map (fragment .oo)
```
```leanOutput ooCheck
Except.ok (Except.ok ())
```

O mesmo programa fica fora do fragmento imperativo, na sua primeira classe.

```lean (name := ooNotImp)
#eval (parseProgram conta).map (fragment .imperative)
```
```leanOutput ooNotImp
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class Conta" })
```

E um programa que devolve um lambda fica fora do orientado a objetos, no tipo que o carrega.

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

# O Que o Monte Custa

%%%
tag := "monte"
%%%

A {secref}[aula-25] reivindicou três coisas para o fragmento imperativo, e o monte custa duas delas.

*Os valores de σ deixam de ser básicos.* Um objeto é um registro de posições com etiqueta de classe, um vetor é um registro de posições e um ponteiro é uma posição. Os três são valores do fragmento, então a memória passa a guardar estrutura além de dado.

*A memória deixa a disciplina de pilha.* A regra `New` aloca as posições dos campos, e nada as libera na saída do bloco. Elas saem de σ em um `delete`, que pode estar em qualquer lugar ou em lugar nenhum, então o tempo de vida de um objeto é decidido pelo programa e não pela forma do seu texto. É precisamente isso que o paradigma queria, porque um objeto que não pudesse sobreviver à função que o construiu serviria de pouco.

*Uma posição pendente torna‑se alcançável.* Com a memória livre da disciplina de pilha, um programa pode guardar um ponteiro para um objeto que já apagou. Core C++ responde com `erro` em vez de comportamento indefinido, e as três entradas são o `delete` duplo, o acesso depois do `delete` e o `delete` por ponteiro para a base sem destrutor virtual, todas da {secref}[aula-19].

Um enunciado sobrevive, e é o que torna o paradigma praticável.

*Toda posição alocada por `new` é alcançada de uma de duas maneiras*, por um ponteiro guardado em variável, campo ou parâmetro, ou por `this` dentro de um método. Não há um terceiro canal, porque o fragmento não tem closure para capturar um ponteiro e levá‑lo adiante, nem variável global onde estacioná‑lo. Raciocinar sobre que parte de um programa pode tocar um objeto reduz‑se, portanto, a seguir os ponteiros, e é isso que faz o encapsulamento significar alguma coisa.

# Encapsulamento e Despacho

%%%
tag := "principios"
%%%

Os dois princípios organizadores do paradigma são ambos restrições ao conhecimento, e ambos são regras de tipos.

O *encapsulamento* diz que a representação de um objeto é conhecida apenas dentro da sua classe. Em Core C++ isso é a regra de visibilidade da {secref}[aula-17], um membro privado é alcançável apenas de um corpo de membro da classe que o declara, verificado em Γ antes de o programa correr. A classe é, portanto, um tipo abstrato de dados cujos membros públicos são a assinatura e cujos campos privados são a representação, e um chamador que respeita a assinatura não pode ser quebrado por uma mudança de representação.

O *despacho* diz que o código que uma chamada executa é conhecido apenas em tempo de execução, pela etiqueta de classe do receptor. Em Core C++ isso é a regra `Dispatch` da {secref}[aula-19], e a sua condição é a marca `virtual`. O chamador conhece, então, a assinatura e não o código, que é a outra metade da mesma ideia, e os dois juntos são o que permite estender um programa com uma classe que o seu autor nunca viu.

O estudo de caso da unidade mostra os dois. O critério da soma é um método `virtual`, então a classe derivada o escolhe, e o acumulador é um campo, então nenhum chamador o alcança a não ser por `junta` e `total`.

```lean (name := caseOo)
def caseOo : String :=
  "class Somador {
   public:
     int acc;
     virtual bool aceita(int i) { return true; }
     void junta(int i) { if (aceita(i)) { acc = acc + i; } }
     int total() { return acc; }
     virtual ~Somador() { }
   };
   class SomadorPar : public Somador {
   public:
     bool aceita(int i) override { return i % 2 == 0; }
   };
   int main() {
     Somador* s = new SomadorPar();
     for (int i = 1; i <= 10; i = i + 1) { s->junta(i); }
     int r = s->total();
     delete s;
     return r;
   }"

#eval (parseProgram caseOo).map fun p => (fragment .oo p, run p)
```
```leanOutput caseOo
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

O método `junta` é declarado uma vez, na base, e chama `aceita`, que a classe derivada redefine. A chamada dentro de `junta` é despachada, então `junta` executa o critério do objeto sobre o qual foi chamado, sem saber qual. Estender o programa com um terceiro critério é uma classe nova e nenhuma mudança em `junta`.

# Despacho e Closure

%%%
tag := "despacho-closure"
%%%

A {secref}[aula-27] escreve o mesmo estudo de caso com um lambda no lugar da classe derivada, e vale pôr os dois lado a lado, porque resolvem duas vezes um mesmo problema.

Um método `virtual` e um closure empacotam comportamento e o levam a um lugar que não sabe qual é. A diferença está no que o carrega. O método viaja dentro de um objeto, junto com o seu estado, e é selecionado por uma etiqueta. O closure viaja sozinho, junto com as cópias que capturou, e é selecionado por ser o valor que é. O fragmento orientado a objetos conserva o primeiro e proíbe o segundo, o fragmento funcional faz o contrário, e Core C++ tem os dois, que é a razão de os dois exemplos do estudo de caso correrem no mesmo interpretador.

A troca aparece nas tabelas da {secref}[aula-29]. O despacho põe o ponto de extensão na hierarquia de tipos, então um comportamento novo é uma classe nova e os sítios de chamada não mudam. O closure põe o ponto de extensão na lista de argumentos, então um comportamento novo é um valor novo e o tipo não muda. Nenhum é melhor, os dois distribuem a mesma liberdade de outra forma.

# Exercícios

%%%
tag := "exercicios-26"
%%%

{exercise "exr-oo-third"}[] Estenda o estudo de caso com um terceiro critério, os múltiplos de três, e confirme que `junta` não muda. Diga que linha da regra `Dispatch` decide a chamada.

{exercise "exr-oo-leak"}[] Escreva um programa do fragmento orientado a objetos que aloca um objeto e nunca o apaga, e um que o apaga duas vezes. Diga o que cada um devolve, e qual dos três resultados `erro` de `delete` o segundo alcança.

{exercise "exr-oo-private"}[] Torne `acc` privado no estudo de caso e acrescente o método de que o programa então precisa. Explique, em termos de Γ, por que a mudança não afeta `main`.

{exercise "exr-oo-reach"}[] A {secref}[monte] afirma que toda posição do monte é alcançada por um ponteiro ou por `this`. Dê o argumento para a regra `Field` e para a regra `MethodCall`, e diga onde um closure o quebraria.

{exercise "exr-oo-vector"}[] Reescreva o estudo de caso de modo que os números venham de um `std::vector<int>` construído com `new`, e diga que posições o programa deixa em σ ao fim e por quê.

{exercise "exr-oo-static"}[] Retire o `virtual` de `aceita` e execute o programa de novo. Explique o resultado pela regra que escolhe o método, e diga o que o verificador de tipos diria se o `override` ficasse.

```lean -show
end Lecture26
```
