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

#doc (Manual) "Aula 6: Tipos Compostos" =>

%%%
tag := "aula-6"
%%%

```lean -show
namespace Lecture6
open CoreCpp
```

Esta aula acrescenta a Core C++ o primeiro tipo composto, a classe com campos. Ela define objetos como registros de posições, dá a `new` o significado de alocar essas posições, estende o juízo de posição aos campos e escreve as regras de tipos e de avaliação de `new C()`, `e->f` e `e.f`. Todo objeto é criado com `new`, vive na memória, é alcançado por um ponteiro e nunca é copiado, e a aula explica o que essa decisão compra.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-6.pt.html).*

# Classes com Campos

%%%
tag := "classes-campos"
%%%

Uma *classe* declara um tipo composto pela lista dos seus *campos*, cada um com tipo e nome. Nesta unidade uma classe tem só campos públicos, e os métodos, os construtores e o controle de acesso chegam na UD V. A declaração abaixo define o tipo `Point` com dois campos inteiros.

```
class Point {
public:
  int x;
  int y;
};
```

Uma declaração de classe é uma declaração de nível superior, ao lado das funções, e a *tabela de classes* do programa leva cada nome de classe à sua lista de campos. O verificador de tipos consulta a tabela para achar o tipo de um campo, e o avaliador a consulta para saber quais posições `new` deve alocar. A declaração é bem formada quando cada campo tem um tipo com valores, então um campo de tipo classe é rejeitado, porque guardaria um objeto por valor. Um campo de tipo ponteiro para classe é aceito, e é o que a {secref}[aula-7] usa para os tipos recursivos.

# Objetos como Registros de Posições

%%%
tag := "objetos"
%%%

Um *objeto* da classe C é um registro com uma posição por campo de C, etiquetado com o nome da classe. O valor guardado em cada posição de campo é o valor do campo, e o registro ocupa uma posição própria. Um *ponteiro* para o objeto é essa posição. O domínio de valores da UD I ganha três formas.

```
v ::= int n | bool b | void
    | loc ℓ                              um ponteiro, a posição de um objeto
    | null                               o valor de nullptr
    | obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]         um objeto, uma posição por campo
```

A escolha de posições para os campos, em lugar de valores, é o que faz da atualização de um campo uma atualização da memória. Escrever `p->x = 3` escreve o valor 3 na posição do campo `x` do objeto que `p` aponta, e todo outro ponteiro para o mesmo objeto vê o valor novo, porque há um registro e não duas cópias. A escolha também mantém intactas as regras da UD I. A atribuição já escreve em uma posição, e a única novidade é que mais expressões denotam posições.

O tipo ponteiro `C*` é o tipo dos ponteiros para objetos de C. Uma variável de tipo `C*` guarda uma posição, nunca um objeto. O tipo `C` em si é um *tipo objeto*, não tem valores no sentido da {secref}[aula-5], e o verificador de tipos rejeita qualquer variável, parâmetro, resultado ou campo de tipo `C`.

```lean (name := objectByValue)
#eval (parseProgram "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
```
```leanOutput objectByValue
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable a" (CoreCpp.Ty.cls "P")))
```

# Criar um Objeto

%%%
tag := "new"
%%%

A expressão `new C()` cria um objeto da classe C. O seu tipo é `C*`, desde que C seja uma classe declarada. A sua avaliação aloca uma posição nova por campo, cada uma com o valor por omissão do tipo do campo, `0` para `int`, `false` para `bool` e `nullptr` para ponteiros, depois aloca o registro em uma posição nova, e avalia para o ponteiro para o registro. Os parênteses vazios são toda a lista de argumentos desta unidade, porque ainda não há construtores.

```
C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
────────────────────────────────── (T-New)
Γ ⊢ new C() : C*

C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ
(ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
──────────────────────────────────────────── (New)
ρ, σ ⊢ new C() ⇒ loc ℓ, σ'
```

Os valores por omissão seguem a inicialização por valor de C++ para `new C()` com parênteses vazios, então um programa de Core C++ e a sua compilação em C++ concordam sobre o conteúdo de um objeto recém‑criado. A regra aloca n + 1 posições, e nenhuma delas é reutilizada, como a memória da UD I já prometia.

# Alcançar um Campo

%%%
tag := "campos"
%%%

O juízo de posição ρ, σ ⊢ e ⇒ₗ ℓ, σ' da {secref}[aula-3] valia só para variáveis. Ele passa a valer para três formas a mais. A desreferência `*e` denota a posição que o ponteiro e guarda. O acesso a campo `e.f` denota a posição do campo f no registro que e denota. A seta `e->f` abrevia `(*e).f` e denota a posição do campo f no objeto que o ponteiro e aponta.

```
ρ, σ ⊢ e ⇒ loc ℓ, σ'                 ρ, σ ⊢ e ⇒ₗ ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────── (LocDeref)    ─────────────────────────────────────────────── (LocField)
ρ, σ ⊢ *e ⇒ₗ ℓ, σ'                   ρ, σ ⊢ e.f ⇒ₗ ℓ_f, σ'

ρ, σ ⊢ e ⇒ loc ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────────────────────────────────── (LocArrow)
ρ, σ ⊢ e->f ⇒ₗ ℓ_f, σ'
```

As regras de tipos espelham as de avaliação. O operando de `->` é um ponteiro para classe, o de `.` é uma classe, o de `*` é um ponteiro, e o tipo do campo vem da tabela de classes.

```
Γ ⊢ e : C*    C tem τ f            Γ ⊢ e : C    C tem τ f           Γ ⊢ e : τ*
──────────────────────── (T-Arrow)  ────────────────────── (T-Field)  ──────────── (T-Deref)
Γ ⊢ e->f : τ                       Γ ⊢ e.f : τ                        Γ ⊢ *e : τ
```

Ler um campo como valor passa pela sua posição. Uma regra, `Read`, cobre `*e`, `e.f`, `e->f` e a indexação da {secref}[aula-7]. A expressão denota uma posição, e o seu valor é o conteúdo dessa posição, que precisa estar viva.

```
ρ, σ ⊢ e ⇒ₗ ℓ, σ'    ℓ ∈ dom σ'
──────────────────────────────── (Read)      e ∈ {*e', e'.f, e'->f, e'[i]}
ρ, σ ⊢ e ⇒ σ'(ℓ), σ'
```

A atribuição a um campo não precisa de regra nova. A regra `Assign` da {secref}[aula-3] avalia o lado direito, depois a posição do lado esquerdo pelo juízo de posição, e escreve. O programa abaixo cria um ponto, atribui aos dois campos e os lê de volta.

```lean (name := ponto)
def ponto : String :=
  "class Point {
  public:
    int x;
    int y;
  };
  int main() {
    Point* p = new Point();
    p->x = 3;
    p->y = p->x + 1;
    return p->x * 10 + p->y;
  }"

#eval (parseProgram ponto).map run
```
```leanOutput ponto
Except.ok (Except.ok (CoreCpp.Val.int 34))
```

Um campo que a classe não tem é um erro estático, achado por `T-Arrow` na tabela de classes antes de qualquer execução.

```lean (name := unknownField)
#eval (parseProgram "class P { public: int x; }; int main() { P* a = new P(); return a->y; }").map check
```
```leanOutput unknownField
Except.ok (Except.error (CoreCpp.TypeError.unknownField "P" "y"))
```

# Uma Derivação com um Objeto

%%%
tag := "trace-objeto"
%%%

A árvore de derivação de um programa pequeno mostra a memória crescer em três posições no `new`, uma para o campo `x`, uma para o registro e uma para a variável `a`, e a atribuição escrever por `LocArrow` na posição do campo.

```lean (name := traceObject)
#eval match parseProgram "class P { public: int x; }; int main() { P* a = new P(); a->x = 3; return a->x; }" with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceObject
    [], {} ⊢ new P() ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}}   (New)
  [], {} ⊢ P* a = new P(); ⇒ normal, [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Decl)
    [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ 3 ⇒ 3, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Lit)
        [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
      [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ ℓ1, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
    [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
  [a ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x = 3; ⇒ normal, [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Assign)
          [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ₗ ℓ2, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocVar)
        [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a ⇒ ℓ1, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Var)
      [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ₗ ℓ0, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (LocArrow)
    [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ a->x ⇒ 3, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Read)
  [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1} ⊢ return a->x; ⇒ ret 3, [a ↦ ℓ2], {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}, ℓ2 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 3, {ℓ0 ↦ 3, ℓ1 ↦ P{x ↦ ℓ0}}   (Call)
```

A variável `a` vive em ℓ2 e guarda ℓ1, o registro vive em ℓ1 e guarda a etiqueta `P` com o campo `x` em ℓ0, e o valor 3 chega a ℓ0. Os três níveis, variável, registro e campo, são todo o modelo de objetos desta disciplina, e a UD V acrescenta métodos e destrutores sobre ele sem o alterar.

# Compartilhamento

%%%
tag := "compartilhamento"
%%%

Dois ponteiros para o mesmo objeto compartilham os seus campos, porque a atribuição copia o ponteiro, uma posição, e não o registro. Escrever por um ponteiro é visível pelo outro, e a igualdade de ponteiros compara posições.

```lean (name := alias)
def alias : String :=
  "class Point { public: int x; int y; };
  int main() {
    Point* a = new Point();
    Point* b = a;
    b->x = 7;
    return a->x + (a == b ? 10 : 0);
  }"

#eval (parseProgram alias).map run
```
```leanOutput alias
Except.ok (Except.ok (CoreCpp.Val.int 17))
```

Em C++ o mesmo programa tem o mesmo resultado, e a decisão de que objetos nunca são copiados é o que retira de Core C++ os construtores de cópia, os operadores de atribuição e as regras sobre quando uma cópia é feita, uma parte grande da norma de C++ que a disciplina mostra em C++ real sem acrescentar ao núcleo.{margin}[ISO/IEC 14882:2017, *Programming Languages, C++*, cláusula 15.] O compartilhamento é também a origem das questões de apelidos que a UD III trata com as referências, e o modelo de registros de posições as responde por inspeção da memória.

# Exercícios

%%%
tag := "exercicios-6"
%%%

{exercise "exr-memoria-apos-new"}[] Escreva a memória depois de `Point* p = new Point(); Point* q = new Point(); q->x = p->x + 5;`, com as posições numeradas como o interpretador as numera, e confira com a árvore de derivação.

{exercise "exr-regras-campo"}[] Construa a derivação de `p->y = p->x + 1` no ambiente e na memória deixados por `Point* p = new Point(); p->x = 3;`, nomeando as regras `Assign`, `LocArrow`, `Read` e `Arith` onde se aplicam.

{exercise "exr-objeto-por-valor"}[] Explique, pelas regras `T-Decl` e `New`, por que `Point q = *p;` é rejeitado, e diga o que C++ faz com essa declaração.

{exercise "exr-compartilhamento"}[] Dê um programa com três ponteiros em que escrever por um muda o valor lido por exatamente um dos outros dois, e desenhe a memória que o explica.

{exercise "exr-campo-classe"}[] A declaração `class Pair { public: Point a; Point b; };` é rejeitada. Reescreva‑a em Core C++, escreva o `main` que cria um par de pontos, e conte as posições que a memória guarda depois dele.

```lean -show
end Lecture6
```
