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

#doc (Manual) "Aula 8: Expressões" =>

%%%
tag := "aula-8"
%%%

```lean -show
namespace Lecture8
open CoreCpp
```

Esta aula fecha a UD II com as expressões como um todo. Ela diz o que é uma expressão e o que a distingue de um comando, fixa a ordem de avaliação e mostra por que a ordem faz parte do significado assim que as expressões têm efeitos, apresenta as duas construções que dispensam a avaliação de um operando, o curto‑circuito e o condicional, e revê o fragmento de Core C++ implementado até aqui como ele está no interpretador em Lean.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-8.pt.html).*

# Expressões e Comandos

%%%
tag := "expressoes-comandos"
%%%

Uma *expressão* é uma construção que se avalia para um valor. Um *comando* é uma construção que se executa pelo seu efeito na memória e não tem valor. Core C++ mantém as duas separadas na gramática, `Expr` e `Cmd`, e nos juízos, ρ, σ ⊢ e ⇒ v, σ′ para expressões e ρ, σ ⊢ c ⇒ r, ρ′, σ′ para comandos. A atribuição é um comando, então `x = y = 1` não é um programa de Core C++, e uma expressão só vira comando seguida de ponto e vírgula, o statement de expressão que descarta o valor.

A separação é uma decisão do projeto da linguagem, e C++ toma a outra, em que a atribuição é uma expressão com valor, e `while ((c = read()) != 0)` é idiomático. Core C++ prefere a separação porque mantém as expressões da UD I livres de efeitos, e porque torna os efeitos desta unidade, os que uma chamada de função produz na memória, mais fáceis de localizar. Uma expressão tem efeito só por uma chamada, e uma chamada tem efeito só pelos ponteiros que recebe.

# Ordem de Avaliação

%%%
tag := "ordem"
%%%

Quando uma expressão não tem efeito na memória, a ordem em que os seus operandos são avaliados não muda o seu valor, e as regras da {secref}[aula-3] poderiam avaliá‑los em qualquer ordem. Quando uma chamada dentro de uma expressão escreve por um ponteiro, a ordem importa. O programa abaixo chama `prox` duas vezes sobre o mesmo contador, e o valor da soma depende de qual chamada roda primeiro.

```lean (name := ordem)
def ordem : String :=
  "class Cont { public: int n; };
  int prox(Cont* c) {
    c->n = c->n + 1;
    return c->n;
  }
  int main() {
    Cont* c = new Cont();
    return prox(c) + 10 * prox(c);
  }"

#eval (parseProgram ordem).map run
```
```leanOutput ordem
Except.ok (Except.ok (CoreCpp.Val.int 21))
```

Core C++ avalia primeiro o operando esquerdo, então a primeira chamada devolve 1 e a segunda devolve 2, e a soma é 1 + 20. A regra `Arith` fixa essa ordem ao encadear a memória, σ entra no operando esquerdo, σ₁ sai dele e entra no direito. C++17 deixa a ordem dos operandos de `+` não especificada, então um compilador C++ pode computar 21 ou 12 para o mesmo programa, e os dois são C++ correto. É o caso que a disciplina escolheu na UD I para mostrar o que significa determinismo. Core C++ tem uma derivação e um resultado, e C++ tem um conjunto de resultados admitidos, do qual Core C++ escolhe um.

As ordens que C++17 fixa, Core C++ mantém. O lado direito de uma atribuição é avaliado antes do esquerdo, o vetor antes do índice em `v[i]`, e a função antes dos argumentos em uma chamada. A {numref}[tbl-ordem] lista as ordens do fragmento.

:::table +header
*
  * Construção
  * Ordem em Core C++
  * Em C++17
*
  * `e₁ ⊕ e₂`, `e₁ ⋈ e₂`
  * esquerdo, depois direito
  * não especificada
*
  * `e₁ = e₂`
  * direito, depois esquerdo
  * fixada, a mesma
*
  * `e[i]`
  * vetor, depois índice
  * fixada, a mesma
*
  * `f(e₁, …, eₖ)`
  * argumentos da esquerda para a direita
  * não especificada
*
  * `e₁ && e₂`, `e₁ || e₂`
  * esquerdo, depois direito se preciso
  * fixada, a mesma
*
  * `e₁ ? e₂ : e₃`
  * condição, depois um ramo
  * fixada, a mesma
:::

{tabcap "tbl-ordem"}[Ordem de avaliação em Core C++ e o que C++17 fixa.]

# Curto‑Circuito

%%%
tag := "curto-circuito"
%%%

A conjunção e a disjunção avaliam o segundo operando só quando o primeiro não decide o resultado. As regras da {secref}[aula-3] o expressam com duas regras por operador, e a consequência é que o segundo operando pode conter uma expressão que seria `erro` se avaliada.

```lean (name := shortAnd)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z != 0 && 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortAnd
Except.ok (Except.ok (CoreCpp.Val.int 0))
```

A divisão por zero nunca roda, porque `z != 0` é falso e `And-False` não tem premissa sobre o segundo operando. A disjunção se comporta simetricamente, e `Or-True` pula o segundo operando quando o primeiro é verdadeiro.

```lean (name := shortOr)
#eval (parseProgram "int main() {
    int z = 0;
    bool b = z == 0 || 10 / z > 1;
    return b ? 1 : 0;
  }").map run
```
```leanOutput shortOr
Except.ok (Except.ok (CoreCpp.Val.int 1))
```

A árvore de derivação mostra o operando pulado como um ramo ausente. Sob o nó `And` há um filho, a derivação de `z != 0`, e nenhuma derivação da divisão.

```lean (name := traceShort)
#eval match parseProgram "int main() { int z = 0; bool b = z != 0 && 10 / z > 1; return b ? 1 : 0; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceShort
    [], {} ⊢ 0 ⇒ 0, {}   (Lit)
  [], {} ⊢ int z = 0; ⇒ normal, [z ↦ ℓ0], {ℓ0 ↦ 0}   (Decl)
          [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z ⇒ₗ ℓ0, {ℓ0 ↦ 0}   (LocVar)
        [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z ⇒ 0, {ℓ0 ↦ 0}   (Var)
        [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ 0 ⇒ 0, {ℓ0 ↦ 0}   (Lit)
      [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z != 0 ⇒ false, {ℓ0 ↦ 0}   (Binary)
    [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ z != 0 && 10 / z > 1 ⇒ false, {ℓ0 ↦ 0}   (And)
  [z ↦ ℓ0], {ℓ0 ↦ 0} ⊢ bool b = z != 0 && 10 / z > 1; ⇒ normal, [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false}   (Decl)
        [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ⇒ₗ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ false}   (LocVar)
      [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ⇒ false, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Var)
      [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ 0 ⇒ 0, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Lit)
    [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ b ? 1 : 0 ⇒ 0, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Cond)
  [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false} ⊢ return b ? 1 : 0; ⇒ ret 0, [z ↦ ℓ0, b ↦ ℓ1], {ℓ0 ↦ 0, ℓ1 ↦ false}   (Return)
[], {} ⊢ main() ⇒ 0, {ℓ0 ↦ 0, ℓ1 ↦ false}   (Call)
```

# A Expressão Condicional

%%%
tag := "condicional"
%%%

O condicional `e₁ ? e₂ : e₃` é a contraparte em expressão do comando `if`. Ele avalia a condição e depois exatamente um ramo, pelas regras `Cond-T` e `Cond-F`, então um ramo que seria `erro` é inofensivo quando não escolhido. Os tipos dos dois ramos precisam concordar, por `T-Cond`, porque a expressão tem um tipo, decida a condição o que decidir em execução.

```lean (name := condSkip)
#eval (parseProgram "int main() { int z = 0; return z == 0 ? 42 : 10 / z; }").map run
```
```leanOutput condSkip
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

O condicional é o que torna possível a recursão sobre um tipo recursivo em uma única expressão, como `soma` na {secref}[aula-7] mostra. Sem ele, o caso base precisaria de um comando `if` e de dois comandos `return`.

# Detalhes da Aritmética

%%%
tag := "aritmetica"
%%%

Dois detalhes da aritmética de `int` fazem parte do significado das expressões. A divisão e o resto truncam em direção a zero, como C++ fixa, então `-7 / 2` é `-3` e `-7 % 2` é `-1`, e a identidade `(a / b) * b + a % b = a` vale também para operandos negativos.

```lean (name := truncation)
#eval (parseProgram "int main() { return -7 / 2 * 10 + -7 % 2; }").map run
```
```leanOutput truncation
Except.ok (Except.ok (CoreCpp.Val.int (-31)))
```

Todo resultado aritmético passa por `int32`, e um resultado fora de 32 bits é `erro`, onde C++ deixa o estouro com sinal indefinido. A verificação é dinâmica, porque os operandos são valores, e é a regra que faz de `int` um tipo de inteiros de 32 bits na semântica e não um tipo de inteiros ilimitados com um nome emprestado de C++.

# O Fragmento em Lean

%%%
tag := "fragmento"
%%%

O fragmento de Core C++ implementado ao fim da UD II tem os tipos básicos, as classes com campos, os ponteiros, os vetores, as expressões desta unidade, os comandos da UD I e as funções de primeira ordem. A {numref}[tbl-fragmento] lista as construções e as funções Lean que lhes dão significado.

:::table +header
*
  * Construção
  * Tipos
  * Avaliação
  * Lean
*
  * literais, variáveis, operadores, condicional
  * `T-Lit` a `T-Cond`
  * `Lit` a `Cond`
  * `Typing.expr`, `Eval.expr`
*
  * `nullptr`, `new C()`, `new std::vector<τ>(n)`
  * `T-Null`, `T-New`, `T-NewVec`
  * `Null`, `New`, `NewVec`
  * `Typing.expr`, `Eval.expr`
*
  * `*e`, `e.f`, `e->f`, `e[i]`
  * `T-Loc…`
  * `Loc…`, `Read`
  * `Typing.lval`, `Eval.lval`
*
  * declaração, atribuição, bloco, `if`, `while`, `for`, `return`
  * `T-Decl` a `T-Ret`
  * `Decl` a `Return`
  * `Typing.cmd`, `Eval.cmd`
*
  * chamada, função, classe, programa
  * `T-Call`, `T-Fun`, `T-Class`, `T-Program`
  * `Call`, `Program`
  * `Typing.fn`, `check`, `runWith`
:::

{tabcap "tbl-fragmento"}[O fragmento de Core C++ ao fim da UD II e a sua implementação.]

Cada regra está no comentário do caso que a implementa, e o [blueprint](https://christianobraga.github.io/corecpp/) apresenta toda regra com um link para o seu código. As unidades seguintes acrescentam construções a este fragmento, referências na UD III, funções como valores na UD IV, métodos e destrutores na UD V, templates e sobrecarga na UD VI, e nenhuma regra desta unidade é reescrita por elas.

# Exercícios

%%%
tag := "exercicios-8"
%%%

{exercise "exr-ordem-resultado"}[] Preveja o valor de `prox(c) * 10 + prox(c) - prox(c)` depois de `Cont* c = new Cont();`, com `prox` como na {secref}[ordem], e depois os dois outros valores que um compilador C++ pode computar para ele.

{exercise "exr-regras-curto-circuito"}[] Escreva as duas regras de `||` na notação da disciplina, e construa a derivação de `z == 0 || 10 / z > 1` em uma memória em que `z` vale 0.

{exercise "exr-atribuicao-expressao"}[] Suponha que a atribuição fosse uma expressão cujo valor é o valor atribuído, como em C++. Escreva as suas regras de tipos e de avaliação, e diga quais programas passariam a tipar que Core C++ rejeita hoje.

{exercise "exr-cond-versus-if"}[] Reescreva `soma` da {secref}[aula-7] com um comando `if` e dois comandos `return`, e compare as duas árvores de derivação para uma lista de um nó.

{exercise "exr-truncamento"}[] Calcule `a / b` e `a % b` para as quatro combinações de sinal de `a = 7` e `b = 2`, pelas regras de Core C++, e confira a identidade `(a / b) * b + a % b = a` em cada caso.

{exercise "exr-extensao-fragmento"}[] Escolha uma construção de C++ que o fragmento não tem, fora as que as próximas unidades anunciam, escreva as suas regras de tipos e de avaliação, e diga se ela poderia entrar sem reescrever uma regra desta unidade.

```lean -show
end Lecture8
```
