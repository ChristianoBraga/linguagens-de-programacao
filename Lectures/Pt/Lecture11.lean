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

#doc (Manual) "Aula 11: Comandos e Controle" =>

%%%
tag := "aula-11"
%%%

```lean -show
namespace Lecture11
open CoreCpp
```

Esta aula trata os comandos de Core C++ como um todo. Ela separa as três formas de controle, sequência, seleção e repetição, dá a cada uma as suas regras, explica o resultado de controle que permite ao `return` interromper uma sequência e um laço, e lê o bloco como a construção que fixa escopo e tempo de vida. As regras foram escritas na {secref}[aula-3], e a aula volta a elas com o vocabulário da UD III e com programas que o interpretador executa.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-11.pt.html).*

# Sequência

%%%
tag := "sequencia"
%%%

O controle mais simples é a *sequência*, um comando depois do outro. A sua regra leva o ambiente e a memória de cada comando ao seguinte, então uma declaração alcança os comandos que a seguem e uma atribuição é vista por eles. A regra tem dois casos, porque um comando pode terminar em `normal` ou em `ret v`, e no segundo caso o resto da sequência não é executado.

```
ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
──────────────────────────────────────────────────── (Seq)
ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
──────────────────────────── (Seq-Ret)
ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁
```

O *resultado de controle* r é o que um comando entrega ao seu contexto. `normal` diz que a execução continua, `ret v` diz que um `return` foi executado com o valor v e que tudo até a chamada envolvente deve parar. O resultado não é um valor da linguagem, e nenhuma expressão o observa. Ele existe na semântica para dar ao `return` um significado sem salto.

# Bloco

%%%
tag := "bloco"
%%%

Um *bloco* é uma sequência entre chaves. A sua regra executa a sequência e depois desfaz o que a sequência fez ao ambiente, mantém o que ela fez à memória, e libera as posições que a sequência alocou.

```
ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ', σ'
──────────────────────────────────────────── (Block)
ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ' ∖ (ρ' ∖ ρ)
```

As três partes da conclusão correspondem a três fatos sobre blocos. O controle r passa, então um `return` dentro de um bloco retorna da função. O ambiente ρ é restaurado, então os nomes declarados no bloco não são visíveis depois dele, que é o *escopo*. A memória perde as posições próprias de ρ' ∖ ρ, então as variáveis declaradas no bloco deixam de existir, que é o *tempo de vida*. A {secref}[aula-10] explicou por que só as ligações próprias são liberadas, para que uma referência nunca retire a posição que nomeia.

Todo ramo de `if`, todo corpo de `while` e de `for`, e todo corpo de função é um bloco, pela gramática. Core C++ não tem comando isolado como ramo, então o escopo é sempre delimitado por chaves e a leitura de um programa nunca depende de onde cai um ponto e vírgula.

# Seleção

%%%
tag := "selecao"
%%%

O comando condicional `if (e) {c₁} else {c₂}` avalia a condição e executa um dos dois blocos. Uma regra por valor da condição, e a memória que a condição produziu é a de que o ramo parte, porque a condição pode chamar uma função com efeitos.

```
ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c₁} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-T)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂

ρ, σ ⊢ e ⇒ bool false, σ₁    ρ, σ₁ ⊢ {c₂} ⇒ r, ρ, σ₂
──────────────────────────────────────────────────── (If-F)
ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂
```

Um `if` sem `else` é um `if` com um segundo bloco vazio, e o analisador produz exatamente isso, como a {secref}[aula-2] mostrou. A condição tem tipo `bool`, e uma condição `int`, que C++ converte, é um erro de tipo em Core C++.

A derivação de uma seleção mostra o bloco do ramo escolhido e nada do outro. Na árvore abaixo o interpretador chama as duas regras de `If`.

```lean (name := ifTrace)
def halve : String :=
  "int main() {
     int x = 2;
     if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
     return x;
   }"

#eval match parseProgram halve with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput ifTrace
ρ₀ = []            σ₀ = {}
ρ₁ = [x ↦ ℓ0]      σ₁ = {ℓ0 ↦ 2}
                   σ₂ = {ℓ0 ↦ 1}
c₀ = if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }

                   𝒟₄                                  𝒟₅                                 𝒟₆
  ρ₀, σ₀ ⊢ int x = 2; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ c₀ ⇒ normal, ρ₁, σ₂    ρ₁, σ₂ ⊢ return x; ⇒ ret 1, ρ₁, σ₂
  ────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 1, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)    ────────────────── (Lit)
  ρ₁, σ₁ ⊢ x ⇒ 2, σ₁                     ρ₁, σ₁ ⊢ 2 ⇒ 2, σ₁
  ─────────────────────────────────────────────────────────────── (Binary)
  ρ₁, σ₁ ⊢ x / 2 ⇒ 1, σ₁

𝒟₂
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────── (Var)    ────────────────── (Lit)
  ρ₁, σ₁ ⊢ x ⇒ 2, σ₁                     ρ₁, σ₁ ⊢ 2 ⇒ 2, σ₁
  ─────────────────────────────────────────────────────────────── (Binary)    ────────────────── (Lit)
  ρ₁, σ₁ ⊢ x % 2 ⇒ 0, σ₁                                                      ρ₁, σ₁ ⊢ 0 ⇒ 0, σ₁
  ──────────────────────────────────────────────────────────────────────────────────────────────────── (Binary)
  ρ₁, σ₁ ⊢ x % 2 == 0 ⇒ true, σ₁

𝒟₃
            𝒟₁              ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x / 2 ⇒ 1, σ₁    ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ─────────────────────────────────────────────────────── (Assign)
  ρ₁, σ₁ ⊢ x = x / 2; ⇒ normal, ρ₁, σ₂
  ──────────────────────────────────────────────────────────────── (Block)
  ρ₁, σ₁ ⊢ { x = x / 2; } ⇒ normal, ρ₁, σ₂

𝒟₄
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 2 ⇒ 2, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 2; ⇒ normal, ρ₁, σ₁

𝒟₅
                𝒟₂                                     𝒟₃
  ρ₁, σ₁ ⊢ x % 2 == 0 ⇒ true, σ₁    ρ₁, σ₁ ⊢ { x = x / 2; } ⇒ normal, ρ₁, σ₂
  ────────────────────────────────────────────────────────────────────────── (If)
  ρ₁, σ₁ ⊢ c₀ ⇒ normal, ρ₁, σ₂

𝒟₆
  ──────────────────── (LocVar)
  ρ₁, σ₂ ⊢ x ⇒ₗ ℓ0, σ₂
  ───────────────────────────── (Var)
  ρ₁, σ₂ ⊢ x ⇒ 1, σ₂
  ─────────────────────────────────── (Return)
  ρ₁, σ₂ ⊢ return x; ⇒ ret 1, ρ₁, σ₂
```

# Repetição

%%%
tag := "repeticao"
%%%

O laço `while (e) {c}` tem três regras. Quando a condição é falsa o laço termina em `normal`. Quando é verdadeira e o corpo termina em `normal`, o laço inteiro é executado de novo na memória que o corpo deixou, e a regra recorre à própria conclusão. Quando o corpo termina em `ret v`, o laço para e entrega `ret v` para cima.

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

A derivação de um laço que executa n vezes encaixa n aplicações de `While-T` e uma de `While-F`, uma dentro da outra, e a sua altura cresce com n. A derivação de um laço que nunca termina não existe, como a {secref}[aula-3] observou, e o interpretador não termina nele. O programa abaixo mostra a terceira regra em ação, um `return` dentro do corpo de um laço cuja condição nunca se torna falsa.

```lean (name := whileRet)
def untilSeven : String :=
  "int main() {
     int i = 0;
     while (true) {
       i = i + 1;
       if (i == 7) { return i; }
     }
   }"

#eval (parseProgram untilSeven).map run
```
```leanOutput whileRet
Except.ok (Except.ok (CoreCpp.Val.int 7))
```

O `return` dentro do `if` dentro do `while` produz `ret 7`. A regra `If-T` o deixa passar, `Seq-Ret` para o corpo, `While-Ret` para o laço, e `Call` o consome. Quatro regras, e nenhum salto.

O laço `for (c₀; e; cₛ) {c}` é definido pelo `while`. O inicializador executa uma vez e a sua variável tem o laço inteiro como escopo, o corpo é um bloco próprio, e o passo executa depois do corpo, fora do escopo do corpo.

```
ρ, σ ⊢ c₀ ⇒ normal, ρ₀, σ₀    ρ₀, σ₀ ⊢ while (e) { {c} cₛ } ⇒ r, ρ₀, σ₁
────────────────────────────────────────────────────────────────────── (For)
ρ, σ ⊢ for (c₀; e; cₛ) {c} ⇒ r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)
```

A conclusão libera a posição da variável do laço, com a mesma leitura de posse de `Block`. Um `for` cujo corpo declara uma variável com o nome da variável do laço a sombreia dentro do corpo e não no passo, porque o corpo é o seu próprio bloco.

# Controle sem Saltos

%%%
tag := "sem-saltos"
%%%

Core C++ não tem `break`, `continue`, `goto` nem exceções. A única saída de um laço é a sua condição ou um `return`, e a única saída de uma função é o seu `return` ou o fim de um corpo `void`. A escolha é deliberada. Cada uma das construções ausentes é uma transferência de controle não local, e cada uma exigiria ou um resultado de controle novo, como `brk` ao lado de `ret`, ou uma semântica com continuações. A disciplina acrescenta um resultado de controle, `ret`, e mostra com ele como os outros entrariam.

O exercício de escrever as regras de `break` é o modo padrão de ver o que o resultado de controle compra. Um resultado `brk` seria produzido pelo comando, deixado passar por `If` e `Seq-Ret`, consumido por `While` como `normal`, e rejeitado pelo verificador de tipos fora de um laço. O último ponto é o que C++ faz, e é o primeiro lugar na disciplina em que o verificador de tipos precisa saber em que construção um comando ocorre.

# Exercícios

%%%
tag := "exercicios-11"
%%%

{exercise "exr-derivacao-while"}[] Construa no papel a derivação de `int i = 0; while (i < 2) { i = i + 1; } return i;` e conte as aplicações de cada regra de `while`.

{exercise "exr-break"}[] Acrescente `break` a Core C++. Dê o resultado de controle que ele produz, as regras de `Seq`, `If` e `While` que o tratam, e a regra de tipos que o rejeita fora de um laço.

{exercise "exr-do-while"}[] Escreva as regras de `do {c} while (e);` sem usar as regras de `while`, e depois mostre como o definir por `while` e um bloco, como o `for` é definido.

{exercise "exr-escopo-for"}[] Em `for (int i = 0; i < n; i = i + 1) { int i = 5; s = s + i; }`, diga que `i` cada ocorrência denota, com a regra `For` e o bloco do corpo. Depois diga o que o programa computa.

{exercise "exr-if-int"}[] C++ aceita `if (x) { … }` com `x` um `int`, e Core C++ rejeita. Escreva a regra que C++ aplica, nomeie a conversão, e explique o que a rejeição compra.

{exercise "exr-return-void"}[] Uma função `void` pode terminar sem `return`. Diga que regra dá à sua chamada o valor `void`, e o que acontece, pelas regras, quando uma função `int` termina sem `return`.

```lean -show
end Lecture11
```
