/-
Slides da Aula 27. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "O Paradigma Funcional" =>

O fragmento sem atualização, e a memória escrita uma vez

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-27___-O-Paradigma-Funcional/)

```lean -show
namespace Slides27
open CoreCpp
```

# §27.1 O fragmento

::::cols
:::col
{lbl}[Admite]

* `int`, `bool`, `void`, `std::function`

* literais, variável, operadores, o condicional

* chamada de função, chamada por valor de função

* o lambda `[=]`

* declaração, bloco, `if`, `return`
:::
:::col
{lbl}[Proíbe]

* a atribuição

* `while`, `for`, expressão como comando

* a referência local, o parâmetro por referência

* classe, chamada de método, `this`

* `new`, `delete`, ponteiros, vetores
:::
::::

* Uma declaração aqui não é uma variável, é uma *ligação*, porque nada pode escrever a posição depois.

# §27.1 O verificador corre

```lean (name := funCheck)
def scale : String :=
  "int sum(int n) {
     return n == 0 ? 0 : n + sum(n - 1);
   }
   std::function<int(int)> scale(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int apply(std::function<int(int)> f, int v) {
     return f(v);
   }
   int main() {
     std::function<int(int)> triple = scale(3);
     int s = sum(4);
     return apply(triple, s);
   }"

#eval (parseProgram scale).map fun p => (fragment .functional p, run p)
```
```leanOutput funCheck
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* Uma função recursiva, uma que devolve um closure e uma que recebe um. Entre elas, o paradigma inteiro.

# §27.2 A memória é escrita uma vez

* A linguagem inteira escreve σ em três lugares, `Assign`, o construtor de um `new` e o destrutor de um `delete`. O fragmento não tem *nenhum dos três*.

* Uma posição recebe o seu valor na declaração ou na ligação de parâmetro e *nunca mais é escrita*.

* Não é o mesmo que dizer que σ não muda. Uma chamada ainda aloca e libera. A afirmação é que *nenhuma posição guarda dois valores na sua vida*.

# §27.2 Duas consequências

* *Transparência referencial.* Uma expressão, duas vezes, sob o mesmo ρ e o mesmo σ, dá o mesmo valor. Um nome pode ser trocado pelo que denota.

* *Indiferença à ordem de avaliação.* Nenhum operando de `e₁ ⊕ e₂` pode mudar σ onde o outro lê, então esquerda para direita e direita para esquerda concordam.

* Um programa do fragmento tem, portanto, *um só significado* sob Core C++ e sob qualquer compilador C++.

* O preço. Sem estrutura de dados, sem atualização no lugar. O fragmento é o paradigma *em miniatura*.

# §27.3 Recursão no lugar da iteração

```lean (name := caseFun)
def caseFun : String :=
  "int sumTo(std::function<bool(int)> p, int n) {
     return n == 0 ? 0 : (p(n) ? n : 0) + sumTo(p, n - 1);
   }
   int main() {
     std::function<bool(int)> even = [=](int i) -> bool { return i % 2 == 0; };
     return sumTo(even, 10);
   }"

#eval (parseProgram caseFun).map fun p => (fragment .functional p, run p)
```
```leanOutput caseFun
Except.ok (Except.ok (), Except.ok (CoreCpp.Val.int 30))
```

* O laço com acumulador vira uma função com parâmetro acumulador, e o *invariante vira a especificação*.

* Uma recursão de profundidade dez põe dez quadros em σ. Sem eliminação de chamada em cauda aqui.

# §27.4 Onde Core C++ para

* *Dados imutáveis.* Uma lista Haskell é construída uma vez e compartilhada. O fragmento não tem dado algum.

* *Preguiça.* A passagem por nome foi uma regra sem contraparte. Haskell avalia por necessidade, então uma lista infinita é utilizável.

* *Tipos algébricos.* Um tipo soma com um `case` é o que a hierarquia de classes e o despacho fazem. Os dois são duais, fácil de estender com casos contra fácil de estender com operações.

* Nenhum dos três muda a semântica. Dizê‑lo com clareza é melhor do que esticar o núcleo para imitá‑los.

# Resumo

* O fragmento funcional *proíbe a atualização*, os laços e o monte, e conserva as expressões, os lambdas e as chamadas.

* A sua memória é *escrita uma vez*, a mais forte das propriedades dos três fragmentos.

* Dela decorrem a *transparência referencial* e a indiferença à ordem de avaliação.

* A iteração vira recursão, e o invariante do laço vira a especificação de uma função.

* Dados imutáveis, preguiça e casamento de padrão são Haskell, e o curso o diz em vez de fingir.

Exercícios: veja as [notas de aula](../pt/Aula-27___-O-Paradigma-Funcional/).

```lean -show
end Slides27
```
