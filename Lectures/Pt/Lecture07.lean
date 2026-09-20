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

#doc (Manual) "Aula 7: Tipos Recursivos e Vetores" =>

%%%
tag := "aula-7"
%%%

```lean -show
namespace Lecture7
open CoreCpp
```

Esta aula constrói os tipos recursivos a partir das classes da {secref}[aula-6], com um campo que aponta para um objeto da mesma classe, e dá a `nullptr` o seu significado de fim de cadeia. Depois acrescenta `std::vector<int>`, o segundo tipo composto da unidade, e o usa para enunciar o princípio da completude de Watt, o princípio de que todo tipo deve ser usável em todo lugar e todo valor deve ser verificável. A desreferência de `nullptr` e o índice fora do vetor são os dois erros de execução da aula.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-7.pt.html).*

# Tipos Recursivos

%%%
tag := "recursivos"
%%%

Um tipo é *recursivo* quando os seus valores contêm valores do mesmo tipo. Em Core C++ um tipo recursivo é uma classe com um campo de tipo ponteiro para a própria classe. A classe `No` abaixo é o nó de uma lista encadeada, com um valor e um ponteiro para o nó seguinte.

```
class No {
public:
  int valor;
  No* prox;
};
```

Um valor de tipo `No*` é `nullptr` ou um ponteiro para um registro cujo campo `prox` é de novo um valor de tipo `No*`. Toda cadeia é finita, porque cada registro foi criado por um `new` que executou antes, e o fim da cadeia é `nullptr`. A recursão está no tipo, e a memória guarda só um número finito de registros.

O literal `nullptr` tem um tipo interno, `nullptr_t`, compatível com todo tipo ponteiro e com nada mais. Ele é a razão de existir a relação ≈ da {secref}[aula-5]. Uma declaração `No* p = nullptr` tipa porque `nullptr_t ≈ No*`, e a comparação `p == nullptr` tipa por `T-Eq`. O seu valor é `null`.

```
────────────────────────── (T-Null)      ──────────────────────────── (Null)
Γ ⊢ nullptr : nullptr_t                  ρ, σ ⊢ nullptr ⇒ null, σ
```

Uma função sobre um tipo recursivo segue a recursão do tipo. A soma de uma lista é zero para `nullptr` e, para um nó, o valor do nó mais a soma do resto.

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

O campo `prox` de um nó recém‑criado é `nullptr`, pelos valores por omissão de `New`, então o segundo nó encerra a lista sem uma atribuição explícita. O condicional avalia só o ramo escolhido, então a chamada recursiva não acontece no fim da lista, e a recursão termina porque toda cadeia é finita.

# A Desreferência de nullptr

%%%
tag := "nullptr"
%%%

As regras `LocDeref` e `LocArrow` da {secref}[aula-6] exigem que o ponteiro avalie para uma posição. Quando ele avalia para `null` não há regra com uma posição como resultado, e o resultado é `erro`. É o primeiro dos dois erros de execução da aula, e o ponto em que Core C++ e C++ se separam. C++ deixa a desreferência de um ponteiro nulo indefinida, e na maioria das máquinas o processo é morto pelo sistema operacional. Core C++ lhe dá o resultado definido `erro`, que o interpretador reporta e que encerra o programa.

```lean (name := nullDeref)
#eval (parseProgram "class No { public: int valor; No* prox; };
  int main() { No* p = nullptr; return p->valor; }").map run
```
```leanOutput nullDeref
Except.ok (Except.error (CoreCpp.Error.nullDereference))
```

A verificação é dinâmica, porque um ponteiro ser nulo depende da execução. Um sistema de tipos que separa ponteiros anuláveis de não anuláveis move parte da verificação para o lado estático, e a UD VI menciona as linguagens que o fazem. Em Core C++ o tipo `No*` inclui `nullptr`, e o programador o testa, como `soma` faz.

# Vetores

%%%
tag := "vetores"
%%%

O tipo `std::vector<τ>` é o segundo tipo composto da unidade, uma sequência de elementos do tipo τ com tamanho fixado na criação. Como todo objeto de Core C++, um vetor é criado com `new`, vive na memória e é alcançado por um ponteiro. A expressão `new std::vector<τ>(n)` avalia o tamanho, aloca uma posição por elemento com o valor por omissão de τ, depois o registro do vetor, e avalia para um ponteiro para ele. O tipo dos elementos precisa ter valores, então um vetor guarda inteiros, booleanos ou ponteiros, nunca objetos.

```
Γ ⊢ n : int    τ tem valores
─────────────────────────────────────────── (T-NewVec)
Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*

ρ, σ ⊢ n ⇒ int k, σ₁    k ≥ 0
(ℓᵢ, σ'ᵢ) = alloc(σ'ᵢ₋₁, default τ) para 1 ≤ i ≤ k,  σ'₀ = σ₁
(ℓ, σ₂) = alloc(σ'ₖ, vec [ℓ₁, …, ℓₖ])
─────────────────────────────────────────────────────── (NewVec)
ρ, σ ⊢ new std::vector<τ>(n) ⇒ loc ℓ, σ₂
```

A indexação `e[i]` denota a posição do elemento i do vetor que e denota. Como o vetor é alcançado por um ponteiro `v`, o elemento se escreve `(*v)[i]`, a desreferência dando o vetor e o índice dando o elemento. O vetor é avaliado antes do índice, a ordem que C++17 fixa para `operator[]`, e o índice precisa cair em $`[0, n)`.

```
Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
───────────────────────────────────── (T-Index)
Γ ⊢ e[i] : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ₁    σ₁(ℓ) = vec [ℓ₀, …, ℓₙ₋₁]
ρ, σ₁ ⊢ i ⇒ int k, σ₂    0 ≤ k < n
──────────────────────────────────────────── (LocIndex)
ρ, σ ⊢ e[i] ⇒ₗ ℓₖ, σ₂
```

Ler e escrever um elemento passam por `Read` e `Assign`, como nos campos. O programa abaixo preenche um vetor de três elementos e o soma com um laço.

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

# O Princípio da Completude

%%%
tag := "completude"
%%%

Watt enuncia o *princípio da completude* para os tipos.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, seção 2.6.] Nenhuma operação deve ser restringida arbitrariamente nos tipos dos seus operandos, e todo valor de um tipo deve ser cidadão de primeira classe, armazenável, passável e devolvível. O princípio tem uma contraparte dinâmica. Um valor deve carregar informação suficiente para que toda operação sobre ele seja verificável. Um vetor que conhece o seu tamanho pode verificar todo índice, e um vetor que não o conhece não pode.

O arranjo de C é o contraexemplo padrão. Um `int a[3]` não carrega o seu tamanho, então `a[3]` lê o que estiver depois do arranjo na memória, e a norma de C++ deixa o resultado indefinido. O vetor de C++ carrega o seu tamanho, mas o seu `operator[]` não o verifica, por velocidade, e a norma deixa o acesso fora dos limites indefinido também. Core C++ toma o vetor porque ele carrega o tamanho, e faz da verificação parte do significado de `[]`. Um índice fora do vetor é o segundo erro de execução da aula.

```lean (name := outOfBounds)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(2);
    return (*v)[2];
  }").map run
```
```leanOutput outOfBounds
Except.ok (Except.error (CoreCpp.Error.outOfBounds 2 2))
```

O próprio tamanho é verificado na criação. Um tamanho negativo é `erro`, onde C++ converte o inteiro negativo em um tamanho sem sinal enorme e lança uma exceção ou esgota a memória.

```lean (name := negativeSize)
#eval (parseProgram "int main() {
    std::vector<int>* v = new std::vector<int>(0 - 1);
    return 0;
  }").map run
```
```leanOutput negativeSize
Except.ok (Except.error (CoreCpp.Error.negativeSize (-1)))
```

Do lado estático o princípio diz que ponteiros e vetores são valores como os outros. Um ponteiro é guardado em variável, passado a função, devolvido de uma e comparado por igualdade, e um vetor alcançado por ponteiro pode ser campo de uma classe, que é como a UD VI constrói uma pilha. A restrição que a disciplina mantém, nenhum objeto por valor, não é uma restrição sobre as operações mas sobre a representação, e o princípio é satisfeito pelos ponteiros.

# Valores por Omissão

%%%
tag := "omissao"
%%%

Todo campo e todo elemento começa com o valor por omissão do seu tipo, `0`, `false` ou `nullptr`. O programa abaixo lê os três valores por omissão de um objeto recém‑criado, e o significado de `New` prevê o resultado antes de ele rodar.

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

# Exercícios

%%%
tag := "exercicios-7"
%%%

{exercise "exr-tamanho-lista"}[] Escreva em Core C++ uma função que conta os nós de uma lista de `No`, e um `main` que constrói uma lista de três nós e devolve a contagem. Execute com o interpretador.

{exercise "exr-memoria-lista"}[] Desenhe a memória depois de o `main` da {secref}[recursivos] construir os seus dois nós, antes da chamada a `soma`, com uma caixa por posição, e marque os registros, os campos e a variável.

{exercise "exr-nullptr-estatico"}[] Explique por que o verificador de tipos não pode rejeitar `No* p = nullptr; return p->valor;`, e proponha uma regra de tipos que o rejeitasse e ainda aceitasse a função `soma`.

{exercise "exr-vetor-inverso"}[] Escreva em Core C++ um `main` que cria um vetor de cinco elementos, o preenche com 1 a 5, o inverte no lugar com um laço e devolve o primeiro elemento. Diga quantas posições a memória guarda ao fim.

{exercise "exr-completude"}[] Para cada item, diga se ele viola o princípio da completude e por quê. Uma linguagem em que funções não devolvem arranjos. Uma linguagem em que arranjos não carregam o tamanho. Uma linguagem em que todo valor pode ser comparado por igualdade.

{exercise "exr-ordem-indice"}[] A regra `LocIndex` avalia o vetor antes do índice. Escreva um programa em que as duas ordens dão resultados diferentes, usando uma função com efeito como índice, e diga qual resultado C++17 fixa.

```lean -show
end Lecture7
```
