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

#doc (Manual) "Aula 18: Objetos e Classes" =>

%%%
tag := "aula-18"
%%%

```lean -show
namespace Lecture18
open CoreCpp
```

Esta aula dá significado a objetos, construtores e chamadas de método. Um objeto continua a ser o que era na {secref}[aula-6], um registro de posições com etiqueta de classe, criado por `new` e alcançado por um ponteiro. O que muda é que `new C(args)` agora roda um construtor, que `this` nomeia o receptor dentro de um corpo de membro, e que uma chamada de método liga `this` e os parâmetros e roda o corpo, exatamente como uma chamada de função. A aula escreve as regras `New`, `This`, `Member` e `MethodCall` e lê a árvore de derivação que o interpretador imprime.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-18.pt.html).*

# Construtores

%%%
tag := "construtores"
%%%

Na {secref}[aula-6] todo campo de um objeto novo recebia o valor por omissão do seu tipo, zero, falso ou `nullptr`, e o cliente preenchia os campos depois. Um *construtor* move esse preenchimento para dentro da classe. Ele é um membro com o nome da classe, com parâmetros e corpo, e `new C(args)` o roda logo depois de alocar os campos, com `this` ligado ao objeto novo.

```lean (name := counter)
def counter : String :=
  "class Contador {
  private:
    int valor;
  public:
    Contador(int inicial) { this->valor = inicial; }
    void incrementa() { valor = valor + 1; }
    int atual() { return valor; }
  };
  int main() {
    Contador* c = new Contador(40);
    c->incrementa();
    c->incrementa();
    return c->atual();
  }"

#eval (parseProgram counter).map run
```
```leanOutput counter
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

A regra de tipos de `new` confere os argumentos com os parâmetros do construtor como uma chamada faz, pela regra `T-Call` da {secref}[aula-13], e dá à expressão o tipo ponteiro. Uma classe sem construtor é criada por `new C()` sozinho, como na UD II.

```
C ↦ class C { … C(p₁ x₁, …, pₖ xₖ) { c } … }    argumentos como em T-Call
──────────────────────────────────────────────────────────────────── (T-New)
Γ ⊢ new C(e₁, …, eₖ) : C*
```

A regra de avaliação aloca os campos com os seus valores por omissão, depois o registro etiquetado, e depois roda o corpo do construtor como uma chamada de membro, {secref}[chamada-de-membro], sobre a posição nova.

```
C ↦ class C { … }    f₁ … fₙ os campos da cadeia de C, a base raiz primeiro
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ    (ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
os construtores da cadeia rodam da base raiz para baixo, cada um com this ↦ ℓ, dando σ''
──────────────────────────────────────────────────────────────────────────────────── (New)
ρ, σ ⊢ new C(e₁, …, eₖ) ⇒ loc ℓ, σ''
```

Os campos da cadeia e a ordem dos construtores importam só com herança, {secref}[aula-19]. Para uma classe sem base a cadeia é a classe sozinha.

# This

%%%
tag := "this"
%%%

Dentro de um corpo de membro a palavra `this` denota o objeto sobre o qual o membro foi chamado, o *receptor*. O seu tipo é um ponteiro para a classe, e ela avalia para a posição do objeto.

```
Γ(this) = C*                       ρ(this) = ℓ
──────────────── (T-This)          ───────────────────────── (This)
Γ ⊢ this : C*                      ρ, σ ⊢ this ⇒ loc ℓ, σ
```

A ligação de `this` em ρ é feita pela chamada, {secref}[chamada-de-membro], e é uma ligação de *referência* no sentido da {secref}[aula-10]. Ela nomeia uma posição que existe antes da chamada, o objeto, e o retorno do membro não a libera. Não há posição cujo conteúdo seja o ponteiro `this`, então `this` não é uma variável, não pode ser atribuído e não denota posição por ⇒ₗ. Ele é um valor ponteiro, e `this->valor` é o campo `valor` do receptor pela regra `LocArrow` da {secref}[aula-6].

Um corpo de membro também pode nomear um campo ou um método do receptor sem `this`. O método `incrementa` acima escreve `valor` diretamente. A regra é um complemento das regras das variáveis. Um nome que não está ligado no contexto, ou no ambiente, e é membro da classe corrente denota o membro de `this`.

```
x ∉ Γ    Γ(this) = C*    Γ ⊢ this->x : τ            x ∉ ρ    ρ(this) = ℓ    σ(ℓ) = obj C [… x ↦ ℓₓ …]
─────────────────────────────────────── (T-VarField)  ──────────────────────────────────────────────── (LocVarField)
Γ ⊢ x : τ                                             ρ, σ ⊢ x ⇒ₗ ℓₓ, σ
```

Um parâmetro ou uma variável local com o nome de um campo esconde o campo, e o campo é então alcançado só por `this`, a regra de C++ também. O construtor de `Contador` acima poderia ter um parâmetro `valor` e o corpo `this->valor = valor;`.

# Chamadas de Membro

%%%
tag := "chamada-de-membro"
%%%

Uma chamada de método `e->m(args)` nomeia um receptor, um método e argumentos. A sua regra de tipos encontra o método na classe do receptor, exige que ele seja visível pela regra `Visible` da {secref}[aula-17], e confere os argumentos como uma chamada faz. A forma `e.m(args)` precisa de um receptor de tipo classe, um objeto denotado por `*p` por exemplo, e `e->m(args)` de um receptor de tipo ponteiro.

```
Γ ⊢ e : C*    C tem τ m(p₁ x₁, …, pₖ xₖ) visível de Γ    argumentos como em T-Call
────────────────────────────────────────────────────────────────────────────── (T-MethodArrow)
Γ ⊢ e->m(e₁, …, eₖ) : τ
```

A avaliação segue a regra `Call` da {secref}[aula-13] com uma ligação a mais. O receptor é avaliado para a posição ℓ do objeto, os argumentos são ligados como em uma chamada, por valor com cópia em posição nova e por referência com ligação à posição do argumento, `this` é ligado a ℓ como referência, e o corpo roda. O retorno libera as cópias e as locais do corpo, e nunca o receptor.

```
para cada i, da esquerda para a direita, com σ'₀ = σ,
  pᵢ = τᵢ     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc(σᵢ, vᵢ)
  pᵢ = τᵢ&    ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ
ρ_m = [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_m, σ'ₖ ⊢ c ⇒ r, ρ', σ''
─────────────────────────────────────────────────────────────── (Member)
membro ℓ (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ por valor} ∪ (ρ' ∖ ρ_m))

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T […]    m ↦ τ m(…) { c } o método da classe de e
membro ℓ (e₁, …, eₖ) ⇒ v, σ'
──────────────────────────────────────────────────────────────────────────────── (MethodCall)
ρ, σ ⊢ e->m(e₁, …, eₖ) ⇒ v, σ'
```

Com `normal` no lugar de `ret v` o resultado é `void` para um método `void` e `erro` nos demais casos, como nas funções. A regra `Member` é compartilhada por métodos, construtores e destrutores. Qual método `m` da classe de `e` roda é a questão do despacho, e a {secref}[aula-19] refina a premissa para métodos virtuais. Nesta aula a classe do objeto e a classe do ponteiro coincidem, e o método é o declarado nessa classe.

O ambiente de um corpo de membro contém `this` e os parâmetros, nada mais. Um método não vê as variáveis de quem o chamou, e quem chama não vê as locais do método, exatamente como nas funções. O que o método vê além dos parâmetros é o objeto, por `this`, e o objeto vive em σ, então as suas alterações sobrevivem ao retorno.

# A Árvore de Derivação de uma Chamada de Método

%%%
tag := "trace-18"
%%%

O interpretador imprime a derivação de um programa com um construtor e uma chamada de método. O receptor dos dois é o mesmo objeto, em ℓ1, e o seu único campo fica em ℓ0.

```lean (name := traceCtor)
def traceCtor : String :=
  "class Caixa {
  private:
    int v;
  public:
    Caixa(int x) { v = x; }
    int dobro() { return v * 2; }
  };
  int main() { Caixa* c = new Caixa(21); return c->dobro(); }"

#eval match parseProgram traceCtor with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput traceCtor
      [], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}} ⊢ 21 ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (Lit)
          [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ₗ ℓ2, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ x ⇒ 21, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (Var)
        [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (LocVar)
      [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 0, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21} ⊢ v = x; ⇒ normal, [this ↦ ℓ1, x ↦ ℓ2], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ2 ↦ 21}   (Assign)
    [], {} ⊢ new Caixa(21) ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (New)
  [], {} ⊢ Caixa* c = new Caixa(21); ⇒ normal, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Decl)
        [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ₗ ℓ3, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
      [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c ⇒ ℓ1, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
            [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ₗ ℓ0, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (LocVar)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v ⇒ 21, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Var)
          [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ 2 ⇒ 2, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Lit)
        [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ v * 2 ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Binary)
      [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return v * 2; ⇒ ret 42, [this ↦ ℓ1], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
    [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ c->dobro() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (MethodCall)
  [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1} ⊢ return c->dobro(); ⇒ ret 42, [c ↦ ℓ3], {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}, ℓ3 ↦ ℓ1}   (Return)
[], {} ⊢ main() ⇒ 42, {ℓ0 ↦ 21, ℓ1 ↦ Caixa{v ↦ ℓ0}}   (Call)
```

As primeiras linhas são o construtor. O campo `v` é alocado em ℓ0 com o zero por omissão e o registro em ℓ1 antes mesmo de o argumento 21 ser avaliado, e por isso a memória da primeira linha já contém os dois. O corpo roda sob o ambiente `[this ↦ ℓ1, x ↦ ℓ2]`, com o parâmetro em uma posição nova ℓ2, e o `v` não qualificado à esquerda da atribuição alcança ℓ0 pela regra `LocVarField`. Quando `New` conclui, ℓ2 saiu da memória e ℓ1 permanece. A chamada de método, na metade de baixo, liga `this` ao mesmo ℓ1, lê `v` por ele e devolve 42, e a memória final contém só o objeto, já que a local `c` de `main` saiu com o retorno da chamada.

# Exercícios

%%%
tag := "exercicios-18"
%%%

{exercise "exr-ctor-order"}[] Na derivação acima os campos são alocados antes de o argumento de `new` ser avaliado. Escreva um programa em que o argumento tem efeito sobre outro objeto e diga se a ordem é observável por um cliente.

{exercise "exr-this-not-lvalue"}[] Explique, pelas regras `This` e `LocVar`, por que `this = nullptr;` dentro de um método é rejeitado, e qual regra o rejeita.

{exercise "exr-hiding"}[] Escreva um construtor cujo parâmetro tem o nome de um campo, atribua o campo por `this` e rode o programa. Depois retire o `this->` e explique, por `T-Var` e `T-VarField`, o que a atribuição faz no lugar.

{exercise "exr-method-env"}[] Escreva um método que menciona uma variável local de quem o chama, rode o verificador de tipos e explique pelo ambiente da regra `Member` por que o nome é desconhecido.

{exercise "exr-two-objects"}[] Crie dois objetos de `Contador` e chame `incrementa` em cada um alternadamente. Desenhe a memória depois de cada chamada e explique por que os dois receptores nunca interferem.

{exercise "exr-trace-read"}[] Na árvore acima, encontre a linha em que ℓ2 sai da memória e a linha em que ℓ3 é criada, e nomeie a regra responsável por cada uma.

```lean -show
end Lecture18
```
