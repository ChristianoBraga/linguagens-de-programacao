/-
Slides da Aula 25. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "O Paradigma Imperativo" =>

Um paradigma como fragmento do núcleo, e o que a restrição compra

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-25___-O-Paradigma-Imperativo/)

```lean -show
namespace Slides25
open CoreCpp
```

# §25.1 Um paradigma como restrição

* Core C++ reúne as construções de três paradigmas ao mesmo tempo. Um programa em um estilo *se mantém longe* das construções dos outros dois.

* Um *fragmento* é um conjunto de construções proibidas. Um programa lhe pertence quando nenhuma declaração menciona uma delas.

```tree
nenhuma declaração de p menciona construção que f proíbe
──────────────────────────────────────────────────────── (Frag)
                        p ∈ f
```

* Não é gramática, não é sistema de tipos, não é outro interpretador. As *regras não mudam*.

* O que muda é o que se pode *dizer* do programa.

# §25.2 O fragmento imperativo

::::cols
:::col
{lbl}[Admite]

* `int`, `bool`, `void`

* variáveis, `auto`, a referência local

* a atribuição

* bloco, `if`, `while`, `for`, `return`

* funções de primeira ordem
:::
:::col
{lbl}[Proíbe]

* tipos classe, ponteiro, vetor, função

* `new`, `delete`

* `this`, acesso a campo, desreferência, indexação

* chamada de método, template de classe

* lambda, `std::function`
:::
::::

# §25.2 O verificador corre

```lean (name := fragCheck)
def mdc : String :=
  "int mdc(int a, int b) {
    while (b != 0) { int t = b; b = a % b; a = t; }
    return a;
  }
  int main() { int x = mdc(48, 18); int& y = x; y = y + 1; return y; }"

#eval (parseProgram mdc).map (fragment .imperative)
```
```leanOutput fragCheck
Except.ok (Except.ok ())
```

```lean (name := fragReject)
def comClasse : String :=
  "class C { public: int v; };
   int main() { C* c = new C(); return c->v; }"

#eval (parseProgram comClasse).map (fragment .imperative)
```
```leanOutput fragReject
Except.ok (Except.error { frag := CoreCpp.Frag.imperative, what := "class", site := "class C" })
```

# §25.3 O que a restrição compra

* *Todo valor de σ é básico.* Nenhuma regra do fragmento produz posição, objeto, vetor ou closure.

* *A memória é uma pilha.* Uma posição entra em uma declaração ou em uma ligação de parâmetro e sai na saída do seu escopo, na ordem inversa.

* *Uma posição pendente é inalcançável.* Uma expressão alcança uma posição só por ρ, e ρ liga um nome só enquanto ela vive.

* Três dos oito resultados `erro` desaparecem, o `delete` duplo, o acesso depois do `delete` e o `delete` por ponteiro para a base.

# §25.3 O preço, e a forma do argumento

* Sem o monte, *nenhuma estrutura de dados sobrevive à função que a construiu*. O vetor fica de fora porque precisa de `new`.

* É por isso que o fragmento orientado a objetos existe, e por isso que C tem ponteiros.

* A forma de toda afirmação desta unidade. O fragmento é menor, então *menos regras se aplicam*, então *mais se pode dizer*.

# §25.4 Controle

* Sequência, seleção, repetição. `While-T` recorre à própria conclusão.

* Um programa é lido como uma *sequência de mudanças de estado no tempo*, e o seu significado é a memória final.

* A Aula 27 lê a mesma computação como um *termo cujo valor não depende do tempo*. Mesmo ρ, mesmo σ, mesmas regras.

# Resumo

* Um *fragmento* é um conjunto de construções proibidas, um predicado sobre a sintaxe abstrata, verificado depois da análise e da tipagem.

* O *fragmento imperativo* conserva os tipos básicos, as variáveis, a atribuição, os comandos e as funções de primeira ordem.

* Ele compra a *disciplina de pilha* em σ, só valores básicos e nenhuma posição pendente.

* Custa o monte, então nenhuma estrutura de dados sobrevive à sua função.

* Proíba isto, ganhe aquilo. Essa troca é a unidade inteira.

Exercícios: veja as [notas de aula](../pt/Aula-25___-O-Paradigma-Imperativo/).

```lean -show
end Slides25
```
