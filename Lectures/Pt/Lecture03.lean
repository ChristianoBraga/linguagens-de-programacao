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

#doc (Manual) "Aula 3: Semântica" =>

%%%
tag := "aula-3"
%%%

```lean -show
namespace Lecture3
open CoreCpp
```

Esta aula introduz a semântica natural, a notação em que a disciplina escreve o significado de cada construção de Core C++. Ela parte dos juízos e das regras de inferência que os alunos conhecem da dedução natural, apresenta os três componentes semânticos, ambiente, memória e valores, e escreve as regras de avaliação das expressões e dos comandos do subconjunto implementado. O interpretador em Lean produz a árvore de derivação de cada execução, e a aula ensina a lê‑la.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-3.pt.html).*

# Juízos e Regras de Inferência

%%%
tag := "juizos"
%%%

Na dedução natural, um *juízo* é uma afirmação que se pode derivar, como "de Γ se deduz φ", e uma *regra de inferência* diz que, de juízos já derivados, as premissas, se deriva outro, a conclusão. Uma *derivação* é uma árvore de aplicações de regras, com axiomas nas folhas e o juízo derivado na raiz. A semântica natural usa exatamente essa forma, com juízos sobre programas em lugar de juízos sobre fórmulas.

Um juízo da semântica natural diz que uma construção, avaliada em um certo contexto, produz um certo resultado. A disciplina escreve os juízos no estilo de sequentes de Kahn,{margin}[G. Kahn, *Natural Semantics*, STACS 87, LNCS 247, pp. 22 a 39, Springer, 1987.] com o contexto à esquerda de ⊢, a construção à direita e o resultado depois de ⇒. Uma regra tem as premissas sobre um traço e a conclusão sob ele, e um nome à direita, pelo qual as derivações a citam.

# Ambiente, Memória e Valores

%%%
tag := "dominios"
%%%

Três componentes descrevem o estado de uma execução de Core C++. O *ambiente* ρ é uma função finita de identificadores em *posições* ℓ, os endereços abstratos da memória. A *memória* σ é uma função finita de posições em *valores*, e o seu domínio é o conjunto das posições vivas. Os valores do subconjunto atual são os inteiros de 32 bits, `int n`, e os booleanos, `bool b`.

A separação entre ambiente e memória é a decisão semântica mais importante da disciplina. Um identificador não denota um valor, denota uma posição, e o valor está na memória. Ler `x` é ler σ(ρ(x)). Atribuir a `x` é escrever em ρ(x). Duas variáveis podem denotar a mesma posição, o que a UD III usa para as referências, e uma posição pode viver depois de o identificador sair de escopo, o que a UD V usa para os objetos. Como o modelo entra desde a primeira regra, nenhuma regra é reescrita quando essas construções chegam.

A disciplina usa quatro juízos, e a {numref}[tbl-juizos] os lista.

:::table +header
*
  * Juízo
  * Leitura
*
  * Γ ⊢ e : τ
  * a expressão e tem tipo τ no contexto de tipos Γ
*
  * ρ, σ ⊢ e ⇒ v, σ′
  * sob ρ e σ, a expressão e avalia para v e produz a memória σ′
*
  * ρ, σ ⊢ e ⇒ₗ ℓ, σ′
  * sob ρ e σ, a expressão e denota a posição ℓ
*
  * ρ, σ ⊢ c ⇒ r, ρ′, σ′
  * sob ρ e σ, o comando c produz o controle r, o ambiente ρ′ e a memória σ′
:::

{tabcap "tbl-juizos"}[Os quatro juízos da semântica de Core C++.]

A memória entra na avaliação das expressões porque uma chamada de função dentro de uma expressão pode alterá‑la. O ambiente de saída de um comando existe para que uma declaração estenda ρ para os comandos seguintes. O *controle* r de um comando é `normal` ou `ret v`, e o segundo caso registra que um `return` foi executado e que o valor v deve subir até a chamada.

Todos os juízos dinâmicos admitem `erro` no lugar do resultado. O `erro` não é um valor da linguagem. Nenhuma sintaxe de Core C++ o produz, testa ou captura, e ele se propaga até o programa inteiro. Ele corresponde, em C++, ao término anormal do programa, e substitui o comportamento indefinido que C++ deixa nesses casos.

# Expressões

%%%
tag := "expressoes"
%%%

Um literal avalia para o seu valor e não altera a memória. O literal inteiro passa pela operação parcial int32, que devolve o inteiro quando ele cabe em 32 bits e `erro` fora.

```
─────────────────────────── (Lit)      ──────────────────────── (BoolLit)
ρ, σ ⊢ n ⇒ int32 n, σ                  ρ, σ ⊢ b ⇒ bool b, σ
```

Uma variável denota a posição que o ambiente lhe dá, e o seu valor é o conteúdo dessa posição na memória. A posição precisa estar viva.

```
ρ(x) = ℓ                              ρ, σ ⊢ x ⇒ₗ ℓ, σ    ℓ ∈ dom σ
────────────────────── (LocVar)       ─────────────────────────────── (Var)
ρ, σ ⊢ x ⇒ₗ ℓ, σ                       ρ, σ ⊢ x ⇒ σ(ℓ), σ
```

Um operador binário aritmético avalia o operando esquerdo, depois o direito na memória que o primeiro produziu, e aplica a operação. A ordem da esquerda para a direita é uma escolha de Core C++ onde C++17 não fixa ordem alguma. A divisão e o resto têm uma premissa a mais, o divisor diferente de zero, e uma regra própria para o divisor zero, com `erro` como resultado.

```
ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂
──────────────────────────────────────────────── (Arith, ⊕ ∈ {+, −, ×})
ρ, σ ⊢ e₁ ⊕ e₂ ⇒ int32 (n₁ ⊕ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂    n₂ ≠ 0
──────────────────────────────────────────────────────── (Div, ⊘ ∈ {/, %})
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ int32 (n₁ ⊘ n₂), σ₂

ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int 0, σ₂
──────────────────────────────────────────────── (DivZero)
ρ, σ ⊢ e₁ ⊘ e₂ ⇒ erro
```

A conjunção e a disjunção têm *curto‑circuito*, então o segundo operando só é avaliado quando o primeiro não decide o resultado. Cada operador tem duas regras, uma por valor do primeiro operando.

```
ρ, σ ⊢ e₁ ⇒ bool false, σ₁
──────────────────────────────── (And-False)
ρ, σ ⊢ e₁ && e₂ ⇒ bool false, σ₁

ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
─────────────────────────────────────────────── (And-True)
ρ, σ ⊢ e₁ && e₂ ⇒ v, σ₂
```

O condicional `e₁ ? e₂ : e₃` segue o mesmo padrão, com uma regra para cada valor da condição, e só o ramo escolhido é avaliado.

A derivação abaixo avalia `x + 41` no ambiente ρ = \[x ↦ ℓ₀\] e na memória σ = \{ℓ₀ ↦ 1\}. Ela aplica `Var`, que por sua vez aplica `LocVar`, depois `Lit`, e por fim `Arith`.

```
  ρ(x) = ℓ₀
  ──────────────── (LocVar)
  ρ, σ ⊢ x ⇒ₗ ℓ₀, σ    ℓ₀ ∈ dom σ
  ──────────────────────────────── (Var)    ─────────────────── (Lit)
  ρ, σ ⊢ x ⇒ int 1, σ                       ρ, σ ⊢ 41 ⇒ int 41, σ
  ─────────────────────────────────────────────────────────────── (Arith)
  ρ, σ ⊢ x + 41 ⇒ int 42, σ
```

# Comandos

%%%
tag := "comandos"
%%%

Uma declaração `τ x = e` avalia o inicializador, aloca uma posição nova com o valor e estende o ambiente. A operação alloc devolve uma posição fora do domínio de σ, e posições nunca são reutilizadas.

```
ρ, σ ⊢ e ⇒ v, σ′    (ℓ, σ″) = alloc(σ′, v)
─────────────────────────────────────────── (Decl)
ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ″
```

Uma atribuição avalia o lado direito, depois a posição do lado esquerdo, e escreve o valor. A ordem, direito antes do esquerdo, é a que C++17 fixa para a atribuição, e Core C++ a mantém.

```
ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
──────────────────────────────────────────────────────── (Assign)
ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
```

Uma sequência de comandos leva o ambiente de saída de cada comando ao seguinte, e um `ret` interrompe a sequência. Um bloco executa a sua sequência, descarta a extensão do ambiente e retira da memória as posições que a sequência declarou. O escopo de uma variável é, assim, a restauração de ρ, e o seu tempo de vida é a retirada da posição de σ.

```
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁

ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ′, σ′
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ′ ∖ (ρ′ ∖ ρ)
```

O `if` tem duas regras, uma por valor da condição, e cada ramo é um bloco. O `while` tem três. Quando a condição é falsa, o laço termina em `normal`. Quando é verdadeira e o corpo termina em `normal`, o laço inteiro é executado de novo, e a regra recorre à própria conclusão. Quando o corpo termina em `ret v`, o laço é interrompido.

```
ρ, σ ⊢ e ⇒ bool false, σ₁
──────────────────────────────────────── (While-F)
ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂    ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
────────────────────────────────────────────────────────────────────────────────────── (While-T)
ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
────────────────────────────────────────────────────── (While-Ret)
ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂
```

O `return e` avalia a expressão e produz o controle `ret v`, que `Seq-Ret` e `While-Ret` propagam até a chamada de função que o consome. A UD IV apresenta a regra da chamada.

# A Árvore de Derivação de uma Execução

%%%
tag := "trace"
%%%

Cada função do interpretador implementa um juízo, e cada caso de cada função implementa uma regra, com a regra escrita no comentário do caso. Quando o rastreamento está ativo, cada aplicação de regra registra a instância da regra que conclui, na profundidade em que ocorre na derivação. O interpretador então desenha a derivação como esta aula escreve as suas regras, as premissas sobre um traço de inferência, a conclusão sob ele e o nome da regra à direita. Uma legenda abre a saída e nomeia os ambientes ρᵢ, as memórias σⱼ e todo sujeito longo demais para um juízo, de modo que um juízo ocupa uma linha. Uma subárvore mais larga que a página é escrita à parte sob um nome 𝒟ₖ, e o lugar de onde veio leva esse nome sobre a conclusão da subárvore, como se faz no papel com uma derivação que não cabe.

```lean (name := traceAssign)
def sum : String :=
  "int main() { int x = 1; x = x + 41; return x; }"

#eval match parseProgram sum with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceAssign
ρ₀ = []            σ₀ = {}
ρ₁ = [x ↦ ℓ0]      σ₁ = {ℓ0 ↦ 1}
                   σ₂ = {ℓ0 ↦ 42}

                   𝒟₂                                      𝒟₃                                      𝒟₄
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ x = x + 41; ⇒ normal, ρ₁, σ₂    ρ₁, σ₂ ⊢ return x; ⇒ ret 42, ρ₁, σ₂
  ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 42, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)    ──────────────────── (Lit)
  ρ₁, σ₁ ⊢ x ⇒ 1, σ₁                     ρ₁, σ₁ ⊢ 41 ⇒ 41, σ₁
  ───────────────────────────────────────────────────────────────── (Binary)
  ρ₁, σ₁ ⊢ x + 41 ⇒ 42, σ₁

𝒟₂
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 1 ⇒ 1, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁

𝒟₃
             𝒟₁               ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x + 41 ⇒ 42, σ₁    ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────────────────────────────────── (Assign)
  ρ₁, σ₁ ⊢ x = x + 41; ⇒ normal, ρ₁, σ₂

𝒟₄
  ──────────────────── (LocVar)
  ρ₁, σ₂ ⊢ x ⇒ₗ ℓ0, σ₂
  ───────────────────────────── (Var)
  ρ₁, σ₂ ⊢ x ⇒ 42, σ₂
  ─────────────────────────────────── (Return)
  ρ₁, σ₂ ⊢ return x; ⇒ ret 42, ρ₁, σ₂
```

A legenda dá os dois ambientes e as três memórias por que esta execução passa. A derivação do alto aplica `Call`, e as suas três premissas são os três comandos do corpo, escritas à parte porque as três juntas ultrapassam a largura da página. A primeira, 𝒟₂, aloca ℓ0 e estende o ambiente para ρ₁. A segunda, 𝒟₃, é a atribuição, e avalia primeiro `x + 41`, como 𝒟₁, a derivação da {secref}[expressoes], e só depois a posição de `x`, na ordem que a regra `Assign` fixa, deixando a memória σ₂. A terceira, 𝒟₄, lê essa memória e produz o controle `ret 42`, que a chamada consome. A chamada libera então as variáveis locais de `main`, a memória da sua conclusão volta a ser σ₀, e o resultado do programa é só o valor 42. No interpretador, os dois casos `Arith` e `Rel` aparecem sob o nome comum `Binary`.

# Erro, Determinismo e Divergência

%%%
tag := "propriedades"
%%%

Três propriedades do conjunto de regras merecem registro. A primeira é que toda derivação de um programa bem tipado termina em um valor ou em `erro`, porque cada construção bem tipada tem regra de avaliação. A divisão por zero e o estouro de `int` terminam em `erro`, e o interpretador devolve esse resultado em lugar de um valor.

```lean (name := divZero)
#eval (parseProgram "int main() { return 10 / 0; }").map run
```
```leanOutput divZero
Except.ok (Except.error (CoreCpp.Error.divisionByZero))
```

```lean (name := overflow)
def overflow : String :=
  "int main() { return 2147483647 + 1; }"

#eval (parseProgram overflow).map run
```
```leanOutput overflow
Except.ok (Except.error (CoreCpp.Error.overflow))
```

A segunda é o *determinismo*. As regras de cada construção têm premissas mutuamente exclusivas, então um programa tem no máximo uma derivação e no máximo um resultado. Em C++ o mesmo programa pode ter mais de um resultado, porque a norma deixa a ordem de avaliação de `f() + g()` a cargo do compilador, e a UD III mostra a outra derivação que um compilador pode escolher.

A terceira é uma limitação. A regra `While-T` recorre à própria conclusão, e um laço que não termina, como `while (true) { }`, não tem derivação finita. A semântica natural, por ser indutiva, não descreve programas que divergem, e nesse caso o interpretador também não termina. Leroy e Grall mostram como uma semântica coindutiva cobre esses programas,{margin}[X. Leroy e H. Grall, *Coinductive big-step operational semantics*, Information and Computation 207(2), 2009, pp. 284 a 304.] e a disciplina enuncia a limitação sem a corrigir.

# Semântica Estática

%%%
tag := "estatica"
%%%

O juízo Γ ⊢ e : τ diz que a expressão e tem tipo τ no contexto Γ, uma função finita de identificadores em tipos. As suas regras têm a mesma forma das regras de avaliação, mas não mencionam memória, porque são verificadas antes da execução. A regra dos operadores aritméticos exige `int` nos dois operandos.

```
Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
──────────────────────────── (T-Arith)
Γ ⊢ e₁ ⊕ e₂ : int
```

O verificador de tipos rejeita `1 + true` antes de qualquer avaliação, e a UD II trata os tipos em detalhe.

```lean (name := typeError)
def sumBool : String := "int main() { return 1 + true; }"

#eval (parseProgram sumBool).map check
```
```leanOutput typeError
Except.ok (Except.error (CoreCpp.TypeError.badOperand "+" (CoreCpp.Ty.bool)))
```

# Exercícios

%%%
tag := "exercicios-3"
%%%

{exercise "exr-derivacao-if"}[] Construa no papel a derivação de `int main() { int x = 2; if (x % 2 == 0) { x = x / 2; } else { x = x - 1; } return x; }` e compare com a árvore que o interpretador imprime.

{exercise "exr-regra-do-while"}[] Escreva as regras de avaliação de `do { c } while (e);`, com o corpo executado antes do primeiro teste, sem usar as regras de `while`.

{exercise "exr-regra-mais-igual"}[] Escreva a regra de `x += e` em duas versões, uma direta e uma que a reduz a `x = x + e`, e diga em que caso as duas dão resultados diferentes se `e` puder alterar a memória.

{exercise "exr-ordem"}[] A regra `Assign` avalia o lado direito antes do esquerdo. Escreva a regra com a ordem contrária e dê um programa de Core C++ em que as duas ordens produzem memórias finais diferentes. Considere que a UD IV acrescenta chamadas de função com efeitos.

{exercise "exr-divergencia"}[] Explique por que `int main() { while (true) { } return 0; }` não tem derivação, e o que acontece quando o interpretador o executa.

{exercise "exr-escopo"}[] Execute `int main() { int x = 1; { int y = 2; x = x + y; } return x; }` com o interpretador e explique, pela regra `Block`, o que acontece com a posição de `y` ao fim do bloco interno. Depois troque `return x` por `return y` e explique a mensagem do verificador de tipos.

```lean -show
end Lecture3
```
