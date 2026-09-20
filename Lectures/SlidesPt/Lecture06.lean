/-
Slides da Aula 6. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Tipos Compostos" =>

Classes com campos, objetos como registros de posições, `new` e acesso a campo

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-6___-Tipos-Compostos/)

```lean -show
namespace Slides6
open CoreCpp
```

# §6.1 Classes com campos

```
class Ponto {
public:
  int x;
  int y;
};
```

* Uma *classe* declara um tipo composto pelos seus *campos*, cada um com tipo e nome. Só campos públicos, métodos e construtores na UD V.

* A *tabela de classes* leva cada nome de classe à sua lista de campos. O verificador lê os tipos dos campos lá, o avaliador lê o que `new` deve alocar.

* Um campo de tipo classe é *rejeitado*, seria um objeto por valor. Um campo de tipo `C*` é aceito.

# §6.2 Objetos como registros de posições

```tree
v ::= int n | bool b | void
    | loc ℓ                              um ponteiro, a posição de um objeto
    | null                               o valor de nullptr
    | obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]         um objeto, uma posição por campo
```

* Uma posição por campo, o registro em uma posição própria, o *ponteiro* é essa posição.

* `p->x = 3` escreve na posição do campo. Todo ponteiro para o objeto vê, *um registro, nenhuma cópia*.

* `Assign` já escreve em uma posição. A única novidade é que *mais expressões denotam posições*.

# §6.2 Nenhum objeto por valor

```lean (name := objectByValue)
#eval (parseProgram "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
```
```leanOutput objectByValue
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable a" (CoreCpp.Ty.cls "P")))
```

* `C*` é um tipo com valores, os ponteiros. `C` é um *tipo objeto*, nenhuma variável, parâmetro, resultado ou campo o tem.

* O que a decisão retira do núcleo. Construtores de cópia, operadores de atribuição, as regras sobre quando uma cópia é feita.

# §6.3 Criar um objeto

```tree
C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
────────────────────────────────── (T-New)
Γ ⊢ new C() : C*

C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
(ℓᵢ, σᵢ) = alloc(σᵢ₋₁, default τᵢ),  σ₀ = σ
(ℓ, σ') = alloc(σₙ, obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])
──────────────────────────────────────────── (New)
ρ, σ ⊢ new C() ⇒ loc ℓ, σ'
```

* Uma posição nova por campo com o *valor por omissão*, `0`, `false`, `nullptr`, depois o registro. n + 1 posições, nunca reutilizadas.

* Os valores por omissão seguem a inicialização por valor de C++ para `new C()`.

# §6.4 Alcançar um campo

```tree
ρ, σ ⊢ e ⇒ loc ℓ, σ'                 ρ, σ ⊢ e ⇒ₗ ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────── (LocDeref)    ─────────────────────────────────────────────── (LocField)
ρ, σ ⊢ *e ⇒ₗ ℓ, σ'                   ρ, σ ⊢ e.f ⇒ₗ ℓ_f, σ'

ρ, σ ⊢ e ⇒ loc ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
────────────────────────────────────────────────── (LocArrow)
ρ, σ ⊢ e->f ⇒ₗ ℓ_f, σ'
```

* O juízo de posição passa a valer para `*e`, `e.f` e `e->f`, que abrevia `(*e).f`.

# §6.4 Tipagem e leitura

```tree
Γ ⊢ e : C*    C tem τ f            Γ ⊢ e : C    C tem τ f           Γ ⊢ e : τ*
──────────────────────── (T-Arrow)  ────────────────────── (T-Field)  ──────────── (T-Deref)
Γ ⊢ e->f : τ                       Γ ⊢ e.f : τ                        Γ ⊢ *e : τ

ρ, σ ⊢ e ⇒ₗ ℓ, σ'    ℓ ∈ dom σ'
──────────────────────────────── (Read)      e ∈ {*e', e'.f, e'->f, e'[i]}
ρ, σ ⊢ e ⇒ σ'(ℓ), σ'
```

* Ler um campo é ler a sua posição, *uma regra* para as quatro formas.

# §6.4 Um ponto

```lean (name := ponto)
def ponto : String :=
  "class Ponto {
  public:
    int x;
    int y;
  };
  int main() {
    Ponto* p = new Ponto();
    p->x = 3;
    p->y = p->x + 1;
    return p->x * 10 + p->y;
  }"

#eval (parseProgram ponto).map run
```
```leanOutput ponto
Except.ok (Except.ok (CoreCpp.Val.int 34))
```

# §6.5 A memória na derivação

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

# §6.6 Compartilhamento

```lean (name := alias)
def alias : String :=
  "class Ponto { public: int x; int y; };
  int main() {
    Ponto* a = new Ponto();
    Ponto* b = a;
    b->x = 7;
    return a->x + (a == b ? 10 : 0);
  }"

#eval (parseProgram alias).map run
```
```leanOutput alias
Except.ok (Except.ok (CoreCpp.Val.int 17))
```

* A atribuição copia o *ponteiro*, uma posição, não o registro. Escrever por um ponteiro é visível pelo outro. A igualdade compara posições.

# Resumo

* Uma *classe* com campos é o primeiro tipo composto. A *tabela de classes* serve ao verificador e a `new`.

* Um *objeto* é um registro de posições com etiqueta de classe, em posição própria, alcançado por um *ponteiro*. Objetos nunca vivem em variáveis.

* `new C()` aloca uma posição por campo com o *valor por omissão* e depois o registro.

* `*e`, `e.f`, `e->f` *denotam posições*, `Read` as lê, `Assign` as escreve, nenhuma regra da UD I mudou.

* Dois ponteiros para um objeto *compartilham* os seus campos.

Exercícios: veja as [notas de aula](../pt/Aula-6___-Tipos-Compostos/).

```lean -show
end Slides6
```
