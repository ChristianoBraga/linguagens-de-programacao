/-
Slides da Aula 20. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Orientação a Objetos" =>

Namespaces, o paradigma orientado a objetos, compilação separada e processos de desenvolvimento

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-20___-Orienta______o-a-Objetos/)

```lean -show
namespace Slides20
open CoreCpp
```

# §20.1 Namespaces

```lean (name := ns)
def ns : String :=
  "namespace Banco {
    class Conta {
    private:
      int saldo;
    public:
      Conta(int inicial) { saldo = inicial; }
      void deposita(int v) { saldo = saldo + v; }
      int consulta() { return saldo; }
    };
  }
  int main() {
    Banco::Conta* c = new Banco::Conta(100);
    c->deposita(20);
    return c->consulta();
  }"

#eval (parseProgram ns).map run
```
```leanOutput ns
Except.ok (Except.ok (CoreCpp.Val.int 120))
```

```lean (name := nsNames)
#eval (parseProgram ns).map fun p => p.classes.map (·.name)
```
```leanOutput nsNames
Except.ok ["Banco::Conta"]
```

* Achatado pelo analisador. Sem regra de tipos nem de avaliação.

# §20.2 O paradigma nas regras

* *Encapsulamento*. `Visible` confina a representação aos métodos.

* *Identidade e estado*. Um objeto é um registro em σ, alcançado por ponteiros. Dois ponteiros para uma posição nomeiam um objeto.

* *Substitutibilidade*. `Subsumption` permite a um cliente de `Forma*` receber qualquer classe derivada, inclusive as escritas depois.

* *Ligação tardia*. A premissa `virtual` de `MethodCall` decide o método pelo objeto, a cada chamada.

{cite}[B. Meyer, *Object-Oriented Software Construction*, 2ª ed., Prentice Hall, 1997.]

# §20.2 Tipo abstrato de dados ou objeto

* Um tipo abstrato de dados tem *uma* representação, e as suas operações a veem, também em outros valores do tipo. A pilha compara duas pilhas lendo as duas.

* Um objeto expõe só a sua *assinatura*, mesmo a objetos da própria classe. Dois objetos podem esconder representações diferentes atrás de uma assinatura.

* Core C++ oferece os dois. A diferença é de projeto.

{cite}[W. R. Cook, *On Understanding Data Abstraction, Revisited*, OOPSLA 2009.]

# §20.3 Compilação separada

```
// pilha.hh                          // pilha.cpp
class Pilha {                         #include "pilha.hh"
private:                              Pilha::Pilha(int n) { … }
  std::vector<int>* itens;            void Pilha::empilha(int x) { … }
  int topo;                           int Pilha::desempilha() { … }
public:                               bool Pilha::vazia() { … }
  Pilha(int n);
  void empilha(int x);
  int desempilha();
  bool vazia();
};
```

* O cabeçalho é a assinatura, o fonte as operações. Uma alteração no fonte religa os clientes, não os recompila.

* Precisa de `#include` e de métodos definidos fora da classe. Core C++ não tem nenhum dos dois. Nenhuma regra nova.

# §20.4 Processos de desenvolvimento

* O tipo abstrato de dados é a *unidade de trabalho*. Especificado, implementado, testado e substituído por conta própria.

* *Sequencial*. Requisitos, projeto, código, teste, com a advertência de que uma passagem única raramente funciona.

* *Iterativo*. Ciclos curtos, cada um entregando uma parte. As assinaturas permitem a uma parte existir antes do resto.

* *Dirigido por testes*. O teste de uma assinatura antes da implementação. O teste é um cliente do tipo.

* A visibilidade é a razão de o contrato ser confiável. Um teste da assinatura testa tudo o que um cliente pode fazer.

{cite}[W. W. Royce, *Managing the Development of Large Software Systems*, IEEE WESCON, 1970. K. Beck, *Test-Driven Development, By Example*, Addison-Wesley, 2002.]

# §20.5 O fragmento da UD V

:::table +header
*
  * Construção
  * Tipos
  * Avaliação
*
  * classe com seções, base, construtor, destrutor
  * `T-Class`
  * a tabela de classes
*
  * membro privado
  * `Visible`
  * nenhuma
*
  * `this`, membro não qualificado
  * `T-This`, `T-VarField`
  * `This`, `LocVarField`
*
  * `new C(args)`
  * `T-New`
  * `New`
*
  * `e->m(args)`
  * `T-MethodArrow`
  * `MethodCall`, `Member`
*
  * `D* ≈ B*`
  * `Subsumption`
  * nenhuma
*
  * `delete e`
  * `T-Delete`
  * `Delete`, `DeleteVec`, `DeleteNull`
:::

# Resumo

* Um `namespace` agrupa classes sob `N::`, achatado pelo analisador.

* O paradigma orientado a objetos se lê nas regras. Encapsulamento, identidade, substitutibilidade, ligação tardia.

* Um tipo abstrato de dados e um objeto diferem em onde vivem as operações.

* A compilação separada é o idioma de C++ para o tipo abstrato de dados na escala dos arquivos, sem regra nova.

* Os processos de desenvolvimento organizam o trabalho em torno de assinaturas, e a visibilidade é o que torna o contrato confiável.

Exercícios: veja as [notas de aula](../pt/Aula-20___-Orienta______o-a-Objetos/).

```lean -show
end Slides20
```
