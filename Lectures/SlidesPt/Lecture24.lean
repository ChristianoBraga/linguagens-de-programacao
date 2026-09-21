/-
Slides da Aula 24. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Inferência de Tipos" =>

Quanto da tipagem uma linguagem assume, de `auto` a Hindley e Milner

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-24___-Infer___ncia-de-Tipos/)

```lean -show
namespace Slides24
open CoreCpp
```

# §24.1 O que `auto` faz

```tree
Γ ⊢ e : τ    τ tem valores    τ ≠ nullptr_t
─────────────────────────────────────────── (T-Auto)
Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]
```

* A regra da UD III, sem caso novo na UD VI. Um ponteiro tem valores e uma instanciação é uma classe.

* O ganho é na *escrita*, não na verificação. A variável tem tipo tão definido quanto um escrito.

```lean (name := autoInst)
def autoInst : String :=
  "template<typename T>
  class Caixa {
  private:
    T v;
  public:
    Caixa(T x) { this->v = x; }
    T abre() { return v; }
  };
  int main() {
    auto c = new Caixa<int>(42);
    auto n = c->abre();
    delete c;
    return n;
  }"

#eval (parseProgram autoInst).map run
```
```leanOutput autoInst
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

# §24.2 A inferência local e o seu limite

* A inferência é *local*. Uma declaração, o tipo de uma expressão que ela já sabe tipar, e nada além.

* Ela nunca corre para trás, de um uso para uma declaração, e nunca resolve um desconhecido.

* Um parâmetro e um resultado são sempre escritos.

```lean (name := autoParam)
#eval parseProgram
  "auto f(auto x) { return x; }
  int main() { return f(1); }"
```
```leanOutput autoParam
Except.error "syntax error at token 0 ('auto'): expected basic type"
```

* C++20 admite o parâmetro, como template de função abreviado, e C++14 o resultado, a partir do `return`. O subconjunto não admite nenhum.

# §24.3 Inferência sobre um programa inteiro

```
comprimento [] = 0
comprimento (x : xs) = 1 + comprimento xs
```

* Hindley e Milner. Uma variável de tipo por desconhecido, *restrições* coletadas do corpo, resolvidas por unificação.

* A resposta é `comprimento :: [a] -> Int`, o tipo *mais geral*, sem anotação alguma.

* Uma implementação para todo `a`, verificada *uma vez*, contra um template expandido e verificado uma vez por instanciação.

* Subtipagem, sobrecarga e um parâmetro usado em dois tipos dentro de um corpo quebram, cada um, a solução mais geral única.

# §24.3 Quanto cada linguagem assume

:::table +header
*
  * Linguagem
  * Inferido
  * Escrito
*
  * C, Pascal
  * nada
  * todo tipo
*
  * Core C++, C++, Java, Rust
  * o tipo de uma declaração local
  * parâmetros e resultados
*
  * Haskell, OCaml
  * todo tipo
  * nada, e uma anotação é uma conferência
:::

* Haskell recupera a sobrecarga pela *classe de tipos*, que mantém a restrição no tipo em vez de a resolver na chamada.

# §24.4 A unidade em um programa

```lean (name := whole)
def whole : String :=
  "template<typename T>
  class Vetor {
  private:
    std::vector<T>* dados;
  public:
    Vetor(int n) { this->dados = new std::vector<T>(n); }
    T& operator[](int i) { return (*dados)[i]; }
    ~Vetor() { delete dados; }
  };
  class Ponto {
  public:
    int x;
    Ponto* operator+(Ponto& o) {
      Ponto* r = new Ponto();
      r->x = x + o.x;
      return r;
    }
  };
  int soma(int a) { return a; }
  int soma(int a, int b) { return a + b; }
  int main() {
    auto v = new Vetor<int>(2);
    (*v)[0] = 20;
    (*v)[1] = soma(20, 2);
    int s = soma((*v)[0]) + (*v)[1];
    Ponto* p = new Ponto();
    p->x = 0;
    Ponto* q = *p + *p;
    int r = s + q->x;
    delete v;
    delete p;
    delete q;
    return r;
  }"

#eval (parseProgram whole).map check
```
```leanOutput whole
Except.ok (Except.ok ())
```

```lean (name := wholeRun)
#eval (parseProgram whole).map run
```
```leanOutput wholeRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

* Um template com um membro que devolve referência, um operador membro, duas sobrecargas e um `auto`.

# Resumo

* `auto` copia o tipo do *inicializador*, e alcança ponteiros e instanciações sem regra nova.

* A inferência é *local*, e parâmetros e resultados são sempre escritos.

* *Hindley e Milner* infere um programa inteiro, e a subtipagem e a sobrecarga são o que atrapalha.

* A unidade em um programa. A instanciação não deixa traço, uma chamada sobrecarregada é uma chamada comum, e um operador e uma indexação são *chamadas de método*.

* `v[i]` é uma chamada de método que devolve `int&`, que o projeto enunciou e a unidade tornou verdadeiro.

Exercícios: veja as [notas de aula](../pt/Aula-24___-Infer___ncia-de-Tipos/).

```lean -show
end Slides24
```
