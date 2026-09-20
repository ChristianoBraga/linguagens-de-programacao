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

#doc (Manual) "Aula 15: Lambdas e Closures" =>

%%%
tag := "aula-15"
%%%

```lean -show
namespace Lecture15
open CoreCpp
```

Esta aula transforma abstrações em valores. Uma expressão lambda `[=](…) -> τ { … }` denota uma função sem nome, e o seu valor é um *closure*, o corpo junto com cópias das variáveis que ele usa. Um closure é guardado em uma variável de tipo `std::function`, passado como argumento, devolvido por uma função e chamado como uma função. A aula escreve as regras do lambda, da chamada através de um valor de função e da captura por cópia, e mostra o efeito por um ponteiro capturado, o único modo pelo qual um closure altera a memória fora de si.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-15.pt.html).*

# Funções como Valores

%%%
tag := "function-values"
%%%

Nas unidades até aqui uma função é uma declaração do programa, nomeada uma vez e chamada por esse nome. Ela não é um valor, nenhuma variável a guarda e nenhum argumento a carrega. O paradigma funcional da {secref}[aula-1] repousa na decisão contrária, funções são valores como inteiros, e Core C++ admite essa decisão na forma que C++17 lhe dá. O tipo `std::function<τ(τ₁, …, τₖ)>` é o tipo dos valores de função com parâmetros dos tipos τ₁ a τₖ e resultado τ, uma variável desse tipo guarda um valor de função, um parâmetro desse tipo recebe um, e uma função pode devolver um.

Os valores desses tipos vêm de *expressões lambda*. A expressão abaixo tem um parâmetro, o tipo de resultado `int`, e um corpo que usa `k`, uma variável da vizinhança.

```
[=](int x) -> int { return k * x; }
```

O `[=]` é a *cláusula de captura*. Ela diz que as variáveis da vizinhança que o corpo usa são copiadas para o valor do lambda no momento em que o lambda é avaliado. C++ também oferece `[&]`, a captura por referência, e Core C++ a exclui, por uma razão que a {secref}[why-copy] dá.

# Onde um Lambda Ocorre

%%%
tag := "positions"
%%%

Um lambda não tem tipo próprio em Core C++. Em C++ todo lambda tem um *tipo de closure* anônimo, distinto de todos os outros, e `auto f = [=]…` dá a `f` esse tipo. Core C++ nunca o forma. A gramática admite um lambda em exatamente três posições, e em cada uma um tipo `std::function` é conhecido, então o lambda é conferido com esse tipo e convertido a ele, como C++ faz quando um lambda encontra um `std::function`.

:::table +header
*
  * Posição
  * Exemplo
  * Tipo esperado vem de
*
  * inicializador de declaração
  * `std::function<int(int)> f = [=](int x) -> int { … };`
  * o tipo declarado
*
  * argumento de chamada
  * `aplica([=](int x) -> int { … }, 3)`
  * o tipo do parâmetro
*
  * expressão de `return`
  * `return [=](int x) -> int { … };`
  * o tipo de resultado da função
:::

{tabcap "tbl-positions"}[As três posições de um lambda e o tipo que cada uma fornece.]

O juízo que faz a verificação se escreve Γ ⊢ e ◁ τ, lido "e é aceitável no tipo τ". Para uma expressão que não é lambda ele é o Γ ⊢ e : τ' comum com τ' ≈ τ. Para um lambda ele é a regra abaixo.

```
Γ' = Γ marcado somente leitura, [x₁ ↦ τ₁, …, xₖ ↦ τₖ]    Γ' ⊢ c ⊣ Γ''    τ, τᵢ com valores
────────────────────────────────────────────────────────────────────────────────────── (T-Lambda)
Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>
```

Os tipos dos parâmetros e do resultado do lambda precisam ser exatamente os do tipo esperado. O corpo é verificado em um contexto em que toda variável da vizinhança está marcada *somente leitura*, porque o corpo verá cópias, e os parâmetros do lambda são variáveis comuns. Um lambda em qualquer outro lugar, como operando ou como inicializador de `auto`, é um erro sintático, porque a gramática põe lambdas só em `ArgExpr`.

```lean (name := autoLambda)
def autoLambda : String :=
  "int main() { auto f = [=](int x) -> int { return x; };
   return f(1); }"

#eval parseProgram autoLambda
```
```leanOutput autoLambda
Except.error "syntax error at token 8 ('[=]'): expected primary expression"
```

# O Closure

%%%
tag := "closure"
%%%

O valor de um lambda é um closure. Ele guarda os parâmetros, o tipo de resultado, o corpo e uma cópia por variável da vizinhança que o corpo menciona, tomada da memória no momento da avaliação.

```
{y₁, …, yₘ} = variáveis livres de c ligadas em ρ, menos os xᵢ
ρ(yⱼ) = ℓⱼ    ℓⱼ ∈ dom σ    wⱼ = σ(ℓⱼ)
──────────────────────────────────────────────────────────────────────────────── (Lambda)
ρ, σ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ⇒ closure(x⃗, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ
```

A memória não muda, o lambda só a lê. O closure guarda *valores*, não posições. Esse é o significado da captura por cópia, e ele tem duas consequências que os programas abaixo tornam visíveis. Uma escrita posterior em uma variável capturada não é vista pelo closure. Um ponteiro capturado continua alcançando o seu objeto em σ, porque a cópia de um ponteiro é a mesma posição.

O programa abaixo declara `soma` com `n` igual a 5, depois atribui 100 a `n`, e chama `soma`. O closure guardou a cópia 5.

```lean (name := captureCopy)
def captureCopy : String :=
  "int main() { int n = 5;
   std::function<int(int)> soma = [=](int x) -> int { return x + n; };
   n = 100; return soma(1); }"

#eval (parseProgram captureCopy).map run
```
```leanOutput captureCopy
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

A marca de somente leitura do contexto rejeita um corpo que escreve em uma variável capturada. A escrita mudaria a cópia, o que C++ também proíbe, já que o operador de chamada de um closure `[=]` é `const`.

```lean (name := constCapture)
def constCapture : String :=
  "int main() { int n = 1;
   std::function<int()> f = [=]() -> int { n = 2; return n; };
   return f(); }"

#eval (parseProgram constCapture).map check
```
```leanOutput constCapture
Except.ok (Except.error (CoreCpp.TypeError.constCapture "n"))
```

# A Chamada de um Valor de Função

%%%
tag := "callfn"
%%%

Uma chamada através de um valor de função avalia a expressão da função para um closure, depois os argumentos da esquerda para a direita, depois aloca posições novas para as cópias capturadas e para os parâmetros, e executa o corpo em um ambiente que contém *só essas ligações*. Nada do ambiente da chamada é visível dentro, exatamente como para uma função nomeada. No retorno as cópias, os parâmetros e as locais do corpo saem da memória.

```
ρ, σ ⊢ e ⇒ closure(x₁ … xₖ, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ₀
ρ, σ₀ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ
(ℓ'ⱼ, ·) = alloc(wⱼ)    (ℓᵢ, ·) = alloc(vᵢ)
ρ_c = [y₁ ↦ ℓ'₁, …, yₘ ↦ ℓ'ₘ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_c, σ' ⊢ c ⇒ ret v, ρ'', σ''
──────────────────────────────────────────────────────────────────────────────── (CallFn)
ρ, σ ⊢ e(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓ'ⱼ, ℓᵢ} ∪ (ρ'' ∖ ρ_c))
```

Quando a expressão chamada é uma variável `f` de tipo função, a chamada `f(…)` é esta regra, e não a chamada de uma função nomeada `f`. Uma variável local esconde uma função de mesmo nome, como em C++. A regra de tipos exige um tipo função e confere cada argumento no tipo do parâmetro correspondente, com ◁, então um lambda pode ele próprio ser argumento.

```
Γ ⊢ e : std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ para cada i
──────────────────────────────────────────────────────────── (T-CallFn)
Γ ⊢ e(e₁, …, eₖ) : τ
```

A árvore abaixo mostra um closure sendo criado, guardado em `f`, lido de volta e chamado. O corpo executa sob \[n ↦ ℓ2, x ↦ ℓ3\], duas posições novas, a cópia de `n` e o parâmetro, e depois da chamada as duas saíram da memória.

```lean (name := lambdaTrace)
def lambdaTrace : String :=
  "int main() { int n = 2;
   std::function<int(int)> f = [=](int x) -> int { return x + n; };
   return f(40); }"

#eval match parseProgram lambdaTrace with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput lambdaTrace
    [], {} ⊢ 2 ⇒ 2, {}   (Lit)
  [], {} ⊢ int n = 2; ⇒ normal, [n ↦ ℓ0], {ℓ0 ↦ 2}   (Decl)
    [n ↦ ℓ0], {ℓ0 ↦ 2} ⊢ [=](int x) -> int { return x + n; } ⇒ closure(int x)[n ↦ 2], {ℓ0 ↦ 2}   (Lambda)
  [n ↦ ℓ0], {ℓ0 ↦ 2} ⊢ std::function<int(int)> f = [=](int x) -> int { return x + n; }; ⇒ normal, [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Decl)
        [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f ⇒ₗ ℓ1, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (LocVar)
      [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f ⇒ closure(int x)[n ↦ 2], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Var)
      [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ 40 ⇒ 40, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Lit)
            [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x ⇒ₗ ℓ3, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (LocVar)
          [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x ⇒ 40, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Var)
            [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ n ⇒ₗ ℓ2, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (LocVar)
          [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ n ⇒ 2, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Var)
        [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ x + n ⇒ 42, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Binary)
      [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40} ⊢ return x + n; ⇒ ret 42, [n ↦ ℓ2, x ↦ ℓ3], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2], ℓ2 ↦ 2, ℓ3 ↦ 40}   (Return)
    [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ f(40) ⇒ 42, {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (CallFn)
  [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]} ⊢ return f(40); ⇒ ret 42, [n ↦ ℓ0, f ↦ ℓ1], {ℓ0 ↦ 2, ℓ1 ↦ closure(int x)[n ↦ 2]}   (Return)
[], {} ⊢ main() ⇒ 42, {}   (Call)
```

# Funções de Ordem Superior

%%%
tag := "higher-order"
%%%

Uma função que recebe ou devolve um valor de função é uma *função de ordem superior*. A função `multiplicador` abaixo devolve um lambda que capturou o seu parâmetro `k`, e `aplica` recebe um valor de função e o chama. A composição calcula 3 vezes 14.

```lean (name := multiplicador)
def multiplier : String :=
  "std::function<int(int)> multiplicador(int k) {
     return [=](int x) -> int { return k * x; };
   }
   int aplica(std::function<int(int)> f, int v) { return f(v); }
   int main() { return aplica(multiplicador(3), 14); }"

#eval (parseProgram multiplier).map run
```
```leanOutput multiplicador
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

O closure devolvido por `multiplicador` sobrevive à chamada que o criou. A sua cópia de `k` é um valor dentro do closure, então nada aponta para uma posição que saiu da memória. É por isso que a captura por cópia é segura em uma linguagem cujas locais morrem com o seu bloco.

Um lambda pode ser argumento diretamente, conferido com o tipo do parâmetro da função chamada.

```lean (name := duasVezes)
def twice : String :=
  "int duasVezes(std::function<int(int)> f, int x) { return f(f(x)); }
   int main() { return duasVezes([=](int x) -> int { return x * x; }, 3); }"

#eval (parseProgram twice).map run
```
```leanOutput duasVezes
Except.ok (Except.ok (CoreCpp.Val.int 81))
```

# Efeitos por um Ponteiro Capturado

%%%
tag := "captured-pointer"
%%%

Um `int` capturado é uma cópia que o closure só pode ler. Um ponteiro capturado é uma cópia de uma posição, e por ela o closure lê e escreve um objeto que vive em σ, fora do closure. A função `contador` abaixo cria um objeto, captura o ponteiro para ele e devolve um closure que incrementa o campo. Cada chamada ao closure altera o mesmo objeto, e o objeto sobrevive ao bloco de `contador` porque objetos criados com `new` vivem até o fim do programa.

```lean (name := contador)
def counter : String :=
  "class Caixa { public: int valor; };
   std::function<int()> contador() {
     Caixa* c = new Caixa();
     c->valor = 0;
     return [=]() -> int { c->valor = c->valor + 1; return c->valor; };
   }
   int main() { std::function<int()> k = contador();
     int primeiro = k(); return k() + k() + primeiro; }"

#eval (parseProgram counter).map run
```
```leanOutput contador
Except.ok (Except.ok (CoreCpp.Val.int 6))
```

As três chamadas devolvem 1, 2 e 3, e a soma é 6. A escrita `c->valor = …` é aceita pelo verificador de tipos, porque escreve no campo do objeto, uma posição alcançada pela cópia de `c`, e não em `c`. É por esse idioma que um closure guarda estado em Core C++, um objeto que ele possui por um ponteiro capturado.

# Por que Só a Captura por Cópia

%%%
tag := "why-copy"
%%%

C++ oferece `[&]`, a captura por referência. O closure guarda então as posições das variáveis capturadas, e uma escrita dentro do corpo altera a variável fora. O problema aparece quando o closure sobrevive ao bloco da variável. A posição saiu da memória, o closure ainda a guarda, e a próxima chamada lê ou escreve uma posição morta, comportamento indefinido em C++. Core C++ exclui `[&]` por essa razão. Todo closure guarda valores, um valor básico capturado é uma cópia, e um ponteiro capturado alcança um objeto que vive tanto quanto o programa. Nenhum closure de Core C++ pode guardar uma posição pendente, e a regra `Lambda` mostra por quê, ela lê σ e guarda o que leu.

Os programas que `[&]` escreveria se escrevem com um ponteiro para um objeto, como `contador` faz. O objeto faz o papel da variável compartilhada, e o seu tempo de vida é o que torna o compartilhamento seguro. A {numref}[tbl-captures] contrasta as duas.

:::table +header
*
  * Captura
  * O closure guarda
  * Escrita no corpo
  * Depois que o bloco externo termina
*
  * `[=]` em um `int`
  * uma cópia do valor
  * rejeitada
  * segura, a cópia está dentro do closure
*
  * `[=]` em um ponteiro
  * uma cópia da posição de um objeto
  * no objeto, permitida
  * segura, o objeto vive em σ
*
  * `[&]`, excluída
  * a posição da variável
  * na variável
  * indefinida em C++
:::

{tabcap "tbl-captures"}[Captura por cópia de valores básicos e de ponteiros, e a captura por referência excluída.]

# Exercícios

%%%
tag := "exercises-15"
%%%

{exercise "exr-compose"}[] Escreva uma função `compoe` que recebe dois valores de tipo `std::function<int(int)>` e devolve a sua composição como um lambda. Explique, pela regra `Lambda`, o que o closure devolvido captura.

{exercise "exr-capture-time"}[] Modifique `captureCopy` de modo que o lambda seja avaliado depois da atribuição `n = 100`, e preveja o resultado antes de executar.

{exercise "exr-adder-array"}[] Escreva uma função que recebe um ponteiro para vetor e um `std::function<int(int)>` e aplica a função a cada elemento no lugar. Diga quais regras das UD II e IV o corpo usa.

{exercise "exr-two-counters"}[] Chame `contador` duas vezes e guarde os dois closures em `k1` e `k2`. Preveja o resultado de `k1() + k1() + k2()` e explique por que os dois closures não compartilham estado.

{exercise "exr-capture-set"}[] A regra `Lambda` captura as variáveis livres do corpo que ρ liga. Escreva um lambda cujo corpo declara uma local com o mesmo nome de uma variável de fora, e explique o que é capturado e se o programa pode observar isso.

{exercise "exr-dangling"}[] Escreva em C++, fora de Core C++, uma função que devolve um lambda `[&]` capturando uma local, chame‑a, e explique pelas regras das UD III e IV qual posição o closure guarda depois do retorno.

```lean -show
end Lecture15
```
