/-
Slides da Aula 18. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Objetos e Classes" =>

Construtores, this, chamadas de método e a árvore de derivação de uma chamada

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-18___-Objetos-e-Classes/)

```lean -show
namespace Slides18
open CoreCpp
```

# §18.1 Construtores

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

* Um membro com o nome da classe. `new C(args)` o roda depois de alocar os campos, com `this` ligado ao objeto.

# §18.1 As regras de new

```tree
C ↦ class C { … C(p₁ x₁, …, pₖ xₖ) { c } … }    argumentos como em T-Call
──────────────────────────────────────────────────────────────────── (T-New)
Γ ⊢ new C(e₁, …, eₖ) : C*

f₁ … fₙ os campos da cadeia de C, a base raiz primeiro
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ)    (ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
os construtores da cadeia rodam da raiz para baixo, cada um com this ↦ ℓ, dando σ''
────────────────────────────────────────────────────────────────────────────────── (New)
ρ, σ ⊢ new C(e₁, …, eₖ) ⇒ loc ℓ, σ''
```

* Campos com os valores por omissão, depois o registro etiquetado, depois os corpos dos construtores.

# §18.2 This

```tree
Γ(this) = C*                       ρ(this) = ℓ
──────────────── (T-This)          ───────────────────────── (This)
Γ ⊢ this : C*                      ρ, σ ⊢ this ⇒ loc ℓ, σ
```

* `this` é o *receptor*. Uma ligação de referência feita pela chamada, nunca liberada pelo retorno.

* Não é variável. Nenhuma posição o guarda, não pode ser atribuído, não denota posição por ⇒ₗ.

* `this->valor` é o campo do receptor por `LocArrow`.

# §18.2 Membros não qualificados

```tree
x ∉ Γ    Γ(this) = C*    Γ ⊢ this->x : τ
─────────────────────────────────────── (T-VarField)
Γ ⊢ x : τ

x ∉ ρ    ρ(this) = ℓ    σ(ℓ) = obj C [… x ↦ ℓₓ …]
──────────────────────────────────────────────── (LocVarField)
ρ, σ ⊢ x ⇒ₗ ℓₓ, σ
```

* Um nome que não é variável e é membro da classe corrente denota o membro de `this`.

* Um parâmetro ou local com o nome de um campo *esconde* o campo, alcançado então só por `this`.

# §18.3 Chamadas de membro

```tree
Γ ⊢ e : C*    C tem τ m(p₁ x₁, …, pₖ xₖ) visível de Γ    argumentos como em T-Call
────────────────────────────────────────────────────────────────────────────── (T-MethodArrow)
Γ ⊢ e->m(e₁, …, eₖ) : τ

ρ_m = [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_m, σ'ₖ ⊢ c ⇒ r, ρ', σ''
─────────────────────────────────────────────────────────────── (Member)
membro ℓ (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ por valor} ∪ (ρ' ∖ ρ_m))

ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T […]    m o método da classe de e
membro ℓ (e₁, …, eₖ) ⇒ v, σ'
─────────────────────────────────────────────────────────────── (MethodCall)
ρ, σ ⊢ e->m(e₁, …, eₖ) ⇒ v, σ'
```

* A regra `Call` com uma ligação a mais. `Member` é compartilhada por métodos, construtores e destrutores.

# §18.3 O que um método vê

* O ambiente de um corpo de membro contém `this` e os parâmetros, *nada mais*.

* Um método não vê as variáveis de quem chama. Quem chama não vê as locais do método.

* O que o método vê além dos parâmetros é o *objeto*, por `this`, e o objeto vive em σ, então as alterações sobrevivem ao retorno.

* Qual `m` roda é o *despacho*, Aula 19. Aqui a classe do objeto e a do ponteiro coincidem.

# §18.4 A árvore de derivação de uma chamada

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

# §18.4 Lendo a árvore

* O campo ℓ0 e o registro ℓ1 existem antes de o argumento 21 ser avaliado.

* O construtor roda sob `[this ↦ ℓ1, x ↦ ℓ2]`. O `v` não qualificado alcança ℓ0 por `LocVarField`. ℓ2 sai no fim de `New`.

* A chamada de método liga `this` ao *mesmo* ℓ1 e devolve 42.

* A memória final contém só o objeto. A local `c` saiu com o retorno de `main`.

# Resumo

* Um *construtor* é executado por `new C(args)` depois de alocar os campos, com `this` ligado ao objeto.

* `this` é o receptor, uma ligação de *referência*, um valor ponteiro e não uma variável.

* Um nome de membro não qualificado dentro de um corpo denota o membro de `this`.

* Uma *chamada de método* é a regra `Call` mais a ligação de `this`. O corpo vê `this`, os parâmetros e o objeto em σ.

* A árvore de derivação mostra cada posição entrando e saindo da memória.

Exercícios: veja as [notas de aula](../pt/Aula-18___-Objetos-e-Classes/).

```lean -show
end Slides18
```
