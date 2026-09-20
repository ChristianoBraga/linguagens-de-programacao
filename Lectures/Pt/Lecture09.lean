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

#doc (Manual) "Aula 9: Variáveis e Armazenamento" =>

%%%
tag := "aula-9"
%%%

```lean -show
namespace Lecture9
open CoreCpp
```

Esta aula abre a UD III, armazenamento e controle, com a variável como objeto. Ela volta ao ambiente ρ e à memória σ da {secref}[aula-3], agora como as duas metades do que uma variável é, nomeia os seis atributos de uma variável e encontra cada um nas regras, e lê a declaração e a atribuição como as duas operações que criam e atualizam o armazenamento. O sombreamento e a saída de um bloco fecham a aula, com a árvore de derivação que o interpretador imprime.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-9.pt.html).*

# Duas Funções em Vez de Uma

%%%
tag := "duas-funcoes"
%%%

O modelo mais simples de variável é uma função de nomes em valores. Nesse modelo `x = x + 1` lê o valor de `x`, soma um e religa `x`, e nada mais existe. Core C++ não usa esse modelo, porque ele não expressa o que o resto da disciplina precisa. Dois nomes para uma variável, um nome que sobrevive a um bloco, um objeto que vários ponteiros alcançam, tudo isso exige um nível entre o nome e o valor.

Esse nível é a *posição*. O ambiente ρ leva cada identificador a uma posição ℓ, e a memória σ leva cada posição a um valor. Uma variável é um par, uma ligação em ρ e uma posição em σ. Ler `x` é ler σ(ρ(x)), e atribuir a `x` é escrever em ρ(x). As duas funções mudam em momentos diferentes. Uma declaração estende ρ e aloca em σ. Uma atribuição muda σ e deixa ρ em paz. A saída de um bloco restaura ρ e encolhe σ.

Watt chama de *armazenáveis* os valores que uma posição pode guardar.{margin}[D. A. Watt, *Programming Language Concepts and Paradigms*, Prentice Hall, 1990, capítulo 3.] Em Core C++ os armazenáveis são os inteiros, os booleanos e os ponteiros, exatamente os tipos com valores da {secref}[aula-5]. Um objeto não é armazenável, ele é um registro de posições, e uma variável de tipo classe não existe. Essa decisão, tomada na {secref}[aula-6], é o que impede um objeto de virar dois depois de uma atribuição.

# Os Atributos de uma Variável

%%%
tag := "atributos"
%%%

Uma variável tem seis atributos, e a semântica dá a cada um o seu lugar. A {numref}[tbl-atributos] os lista.

:::table +header
*
  * Atributo
  * Onde vive
  * Fixado por
*
  * identificador
  * a chave em ρ e em Γ
  * a declaração
*
  * posição
  * ρ(x)
  * a declaração, por alloc
*
  * valor
  * σ(ρ(x))
  * o inicializador, depois cada atribuição
*
  * tipo
  * Γ(x)
  * a declaração, verificado estaticamente
*
  * escopo
  * os comandos em que x está em ρ
  * o bloco que declara x
*
  * tempo de vida
  * o intervalo em que ρ(x) está em dom σ
  * de alloc à saída do bloco
:::

{tabcap "tbl-atributos"}[Os seis atributos de uma variável e o seu lugar na semântica.]

O identificador, o tipo e o escopo são atributos *estáticos*. O verificador de tipos os conhece sem executar o programa, e a {secref}[aula-5] mostrou Γ levando o identificador e o tipo pelos comandos de um bloco. A posição, o valor e o tempo de vida são *dinâmicos*. Eles só existem em uma derivação do juízo de avaliação, e duas execuções da mesma declaração, em duas chamadas da mesma função, recebem duas posições.

Escopo e tempo de vida coincidem para uma variável local de Core C++, porque o bloco que declara a variável é o bloco que libera a sua posição. Eles se separam na próxima aula, quando uma referência dá a uma posição um segundo nome com escopo próprio, e já se separaram na {secref}[aula-6] para os objetos, que vivem até o fim do programa enquanto os ponteiros que os alcançam vêm e vão.

# Declaração

%%%
tag := "declaracao"
%%%

A declaração `τ x = e` cria uma variável. A sua regra de tipos exige que o inicializador tenha o tipo declarado, ou um tipo compatível com ele, e estende Γ. A sua regra de avaliação avalia o inicializador, aloca uma posição nova com o valor e estende ρ. A gramática exige o inicializador, então nenhuma variável guarda um valor desconhecido, uma decisão que a {secref}[aula-2] discutiu.

```
Γ ⊢ e : τ'    τ' ≈ τ    τ tem valores
─────────────────────────────────────── (T-Decl)
Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ v, σ'    (ℓ, σ″) = alloc(σ', v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

A operação alloc devolve uma posição fora do domínio de σ. Posições nunca são reutilizadas, então ℓ identifica esta variável pelo resto da execução, mesmo depois de o bloco a liberar. O ambiente de saída ρ\[x ↦ ℓ\] é o que faz a declaração alcançar os comandos seguintes, pela regra de sequência da {secref}[aula-3].

Uma declaração sem inicializador é um erro sintático, não um erro de tipo, porque a gramática de `LocalDecl` não tem alternativa para ela.

```lean (name := noInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput noInit
Except.error "syntax error at token 7 (';'): expected '='"
```

# Atribuição

%%%
tag := "atribuicao"
%%%

A atribuição `e₁ = e₂` atualiza uma variável, ou qualquer outra posição. O seu lado esquerdo precisa denotar uma posição, pelo juízo Γ ⊢ₗ e₁ : τ, e o seu lado direito precisa ter um tipo compatível. A sua regra de avaliação avalia primeiro o lado direito, depois a posição do lado esquerdo, e escreve o valor ali. A posição precisa estar viva.

```
Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ    τ tem valores
───────────────────────────────────────────────────── (T-Assign)
Γ ⊢ e₁ = e₂ ⊣ Γ

ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

O tipo de uma variável nunca muda, e o verificador de tipos rejeita uma atribuição de um valor de outro tipo antes de o programa executar.

```lean (name := assignBool)
#eval (parseProgram "int main() { int x = 1; x = true; return x; }").map check
```
```leanOutput assignBool
Except.ok (Except.error (CoreCpp.TypeError.mismatch "assignment to x" (CoreCpp.Ty.int) (CoreCpp.Ty.bool)))
```

A atribuição é um comando em Core C++, não uma expressão, então ela não tem valor e `x = y = 1` não é um programa. A {secref}[aula-8] deu as razões da separação. A consequência para esta aula é que uma atualização da memória acontece só em um comando, uma declaração ou uma atribuição, ou dentro de uma chamada de função, e nunca no meio de uma expressão aritmética sem chamada.

# Sombreamento e Saída de Bloco

%%%
tag := "sombreamento"
%%%

Um bloco pode declarar uma variável com o nome de uma variável de um bloco externo. A ligação nova entra na frente de ρ, e a busca a encontra primeiro, então a variável interna *sombreia* a externa pelo resto do bloco. As duas variáveis têm posições diferentes, e a externa mantém o seu valor. Quando o bloco termina, a ligação interna sai de ρ e a posição interna sai de σ, e o nome volta a denotar a variável externa.

```lean (name := shadowRun)
def shadow : String :=
  "int main() {
     int x = 1;
     { int x = 10; x = x + 1; }
     return x;
   }"

#eval (parseProgram shadow).map run
```
```leanOutput shadowRun
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

A árvore de derivação mostra as duas variáveis lado a lado. Dentro do bloco ρ tem duas ligações para `x`, a interna em ℓ1, e a atribuição escreve em ℓ1. A regra `Block` devolve o ρ externo e uma memória sem ℓ1.

```lean (name := shadowTrace)
#eval match parseProgram shadow with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput shadowTrace
    [], {} ⊢ 1 ⇒ 1, {}   (Lit)
  [], {} ⊢ int x = 1; ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Decl)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ 10 ⇒ 10, {ℓ0 ↦ 1}   (Lit)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int x = 10; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Decl)
          [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
        [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ 10, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Var)
        [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ 1 ⇒ 1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Lit)
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x + 1 ⇒ 11, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (Binary)
      [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x ⇒ₗ ℓ1, {ℓ0 ↦ 1, ℓ1 ↦ 10}   (LocVar)
    [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 10} ⊢ x = x + 1; ⇒ normal, [x ↦ ℓ0, x ↦ ℓ1], {ℓ0 ↦ 1, ℓ1 ↦ 11}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int x = 10; x = x + 1; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Block)
      [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ₗ ℓ0, {ℓ0 ↦ 1}   (LocVar)
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ x ⇒ 1, {ℓ0 ↦ 1}   (Var)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ return x; ⇒ ret 1, [x ↦ ℓ0], {ℓ0 ↦ 1}   (Return)
[], {} ⊢ main() ⇒ 1, {ℓ0 ↦ 1}   (Call)
```

O ambiente impresso lista as ligações da mais antiga para a mais nova, e a busca as lê da mais nova para a mais antiga, por isso `x ⇒ₗ ℓ1` dentro do bloco. C++ tem a mesma regra para o sombreamento e a mesma para o fim de um bloco, em que o armazenamento da variável interna é liberado. A diferença é que Core C++ torna a liberação visível em σ, e qualquer acesso posterior a ℓ1 seria `erro`, enquanto C++ deixa esse acesso indefinido. A próxima aula mostra como uma referência produz esse acesso em C++ e por que ela não o produz em Core C++.

# Exercícios

%%%
tag := "exercicios-9"
%%%

{exercise "exr-atributos-traco"}[] Para o programa da {secref}[sombreamento], dê os seis atributos de cada uma das duas variáveis chamadas `x`, e diga em que linha da árvore de derivação cada atributo dinâmico é fixado.

{exercise "exr-uma-funcao"}[] Tome o modelo de variável como uma função de nomes em valores, sem posições, e dê um programa de Core C++ da UD II cujo significado esse modelo não expressa. Explique que atributo falta.

{exercise "exr-alloc-sem-reuso"}[] Posições nunca são reutilizadas. Dê um programa em que um bloco declara uma variável, termina, e um bloco posterior declara outra, e escreva a memória depois de cada bloco. Diga o que mudaria se alloc pudesse devolver uma posição liberada.

{exercise "exr-ordem-decl"}[] A regra `Decl` avalia o inicializador antes de alocar. Escreva a regra que aloca primeiro e avalia depois, e dê um programa em que as duas regras diferem. Considere um inicializador que menciona a variável declarada.

{exercise "exr-atributos-estaticos"}[] Para cada atributo da {numref}[tbl-atributos], diga se o verificador de tipos de Core C++ precisa dele, e nomeie a regra de Γ ⊢ c ⊣ Γ' que o lê ou o escreve.

{exercise "exr-cpp-nao-inicializada"}[] C++ aceita `int x; return x;` e deixa o resultado indefinido. Explique como Core C++ remove o caso, e diga se o remove estática ou dinamicamente.

```lean -show
end Lecture9
```
