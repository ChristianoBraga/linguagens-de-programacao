/-
Slides da Aula 7. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Tipos Recursivos e Vetores" =>

Listas encadeadas, `nullptr`, `std::vector` e o princípio da completude

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-7___-Tipos-Recursivos-e-Vetores/)

{cite}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, seção 2.6.]

```lean -show
namespace Slides7
open CoreCpp
```

# §7.1 Tipos recursivos

```
class No {
public:
  int valor;
  No* prox;
};
```

* Um tipo é *recursivo* quando os seus valores contêm valores do mesmo tipo. Em Core C++, uma classe com um campo de tipo *ponteiro para a própria classe*.

* Um `No*` é `nullptr` ou um ponteiro para um registro cujo `prox` é de novo um `No*`. Toda cadeia é *finita*, cada registro veio de um `new` que rodou antes.

* A recursão está no *tipo*. A memória guarda um número finito de registros.

# §7.1 nullptr

```tree
────────────────────────── (T-Null)      ──────────────────────────── (Null)
Γ ⊢ nullptr : nullptr_t                  ρ, σ ⊢ nullptr ⇒ null, σ
```

* `nullptr` tem o tipo interno `nullptr_t`, compatível com *todo tipo ponteiro* e nada mais. É para isso que existe a relação ≈.

* `No* p = nullptr` tipa porque `nullptr_t ≈ No*`. `p == nullptr` tipa por `T-Eq`.

# §7.1 Uma função sobre um tipo recursivo

```lean (name := lista)
def lista : String :=
  "class No {
  public:
    int valor;
    No* prox;
  };
  int soma(No* p) {
    return p == nullptr ? 0 : p->valor + soma(p->prox);
  }
  int main() {
    No* lista = new No();
    lista->valor = 1;
    lista->prox = new No();
    lista->prox->valor = 2;
    return soma(lista);
  }"

#eval (parseProgram lista).map run
```
```leanOutput lista
Except.ok (Except.ok (CoreCpp.Val.int 3))
```

* O segundo nó encerra a lista porque `prox` vale `nullptr` por omissão. O condicional avalia só o ramo escolhido, a recursão para.

# §7.2 A desreferência de nullptr

```lean (name := nullDeref)
#eval (parseProgram "class No { public: int valor; No* prox; };
  int main() { No* p = nullptr; return p->valor; }").map run
```
```leanOutput nullDeref
Except.ok (Except.error (CoreCpp.Error.nullDereference))
```

* `LocDeref` e `LocArrow` precisam de uma *posição*. Com `null` não há regra, o resultado é `erro`.

* C++ deixa *indefinido*, o processo normalmente é morto. Core C++ dá um *resultado definido* que encerra o programa.

* A verificação é *dinâmica*. Um sistema de tipos com ponteiros não anuláveis move parte dela para o lado estático.

# §7.3 Vetores

```tree
Γ ⊢ n : int    τ tem valores
─────────────────────────────────────────── (T-NewVec)
Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*

ρ, σ ⊢ n ⇒ int k, σ₁    k ≥ 0
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, default τ) para 1 ≤ i ≤ k,  σ'₀ = σ₁
(ℓ, σ₂) = alloc(σ'ₖ, vec [ℓ₁, …, ℓₖ])
─────────────────────────────────────────────────────── (NewVec)
ρ, σ ⊢ new std::vector<τ>(n) ⇒ loc ℓ, σ₂
```

* Uma sequência de elementos com tamanho fixado na criação. Criado com `new`, na memória, alcançado por ponteiro, *como todo objeto*.

* Os elementos têm valores, inteiros, booleanos ou ponteiros, *nunca objetos*.

# §7.3 Indexação

```tree
Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
───────────────────────────────────── (T-Index)
Γ ⊢ e[i] : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ₁    σ₁(ℓ) = vec [ℓ₀, …, ℓₙ₋₁]
ρ, σ₁ ⊢ i ⇒ int k, σ₂    0 ≤ k < n
──────────────────────────────────────────── (LocIndex)
ρ, σ ⊢ e[i] ⇒ₗ ℓₖ, σ₂
```

* `(*v)[i]`, a desreferência dá o vetor, o índice dá o elemento. Vetor antes do índice, a ordem que C++17 fixa.

* `e[i]` *denota uma posição*, então `Read` e `Assign` funcionam como nos campos.

# §7.3 Somar um vetor

```lean (name := vetor)
def vetor : String :=
  "int main() {
    std::vector<int>* v = new std::vector<int>(3);
    (*v)[0] = 1;
    (*v)[1] = 2;
    (*v)[2] = 3;
    int s = 0;
    for (int i = 0; i < 3; i = i + 1) { s = s + (*v)[i]; }
    return s;
  }"

#eval (parseProgram vetor).map run
```
```leanOutput vetor
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

# §7.4 O princípio da completude

* *Nenhuma operação restringida arbitrariamente* nos tipos dos operandos. *Todo valor de primeira classe*, armazenável, passável, devolvível.

* A contraparte dinâmica. Um valor carrega informação suficiente para que *toda operação sobre ele seja verificável*.

* O arranjo de C `int a[3]` não carrega o tamanho, `a[3]` é indefinido. O vetor de C++ o carrega mas `operator[]` não o verifica, indefinido também.

* Core C++ toma o vetor *porque ele carrega o tamanho*, e faz da verificação parte do significado de `[]`.

# §7.4 Fora dos limites e tamanho negativo

```lean (name := outOfBounds)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(2);
    return (*v)[2];
  }").map run
```
```leanOutput outOfBounds
Except.ok (Except.error (CoreCpp.Error.outOfBounds 2 2))
```

```lean (name := negativeSize)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(0 - 1);
    return 0;
  }").map run
```
```leanOutput negativeSize
Except.ok (Except.error (CoreCpp.Error.negativeSize (-1)))
```

# §7.5 Valores por omissão

```lean (name := campos)
def campos : String :=
  "class Reg { public: int n; bool ok; Reg* prox; };
  int main() {
    Reg* r = new Reg();
    return r->n + (r->ok ? 10 : 1) + (r->prox == nullptr ? 100 : 0);
  }"

#eval (parseProgram campos).map run
```
```leanOutput campos
Except.ok (Except.ok (CoreCpp.Val.int 101))
```

* `0`, `false`, `nullptr`. O significado de `New` prevê o resultado antes de o programa rodar.

# Resumo

* Um *tipo recursivo* é uma classe com um ponteiro para si mesma. As cadeias são finitas e terminam em `nullptr`, cujo tipo `nullptr_t` é compatível com todo ponteiro.

* Desreferenciar `nullptr` é `erro`, *dinâmico*, onde C++ é indefinido.

* Um *vetor* é um objeto com uma posição por elemento, criado com `new` e indexado por `(*v)[i]`, que denota uma posição.

* O *princípio da completude*. Todo valor de primeira classe, toda operação verificável. O vetor carrega o tamanho, o arranjo de C não.

* Fora dos limites e tamanho negativo são `erro`. Campos e elementos começam com o *valor por omissão* do tipo.

Exercícios: veja as [notas de aula](../pt/Aula-7___-Tipos-Recursivos-e-Vetores/).

```lean -show
end Slides7
```
