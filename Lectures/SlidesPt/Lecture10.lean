/-
Slides da Aula 10. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Referências e Apelidos" =>

Um segundo nome para uma posição, ligações próprias e de referência

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-10___-Refer___ncias-e-Apelidos/)

```lean -show
namespace Slides10
open CoreCpp
```

# §10.1 Um segundo nome para uma posição

* `int& y = x` não aloca. Liga `y` à posição de `x`.

* Dois nomes, uma posição, um valor. Uma escrita por qualquer dos dois é vista pelo outro, *aliasing*.

```
LocalDecl ::= 'auto' VarId '=' Expr
            | Type '&'? VarId '=' Expr
```

* Continua LL(1). Depois de `Type` o token seguinte é `&` ou um identificador de variável.

```lean (name := parseRef)
#eval parseStatement "int& y = x;"
```
```leanOutput parseRef
Except.ok (CoreCpp.Cmd.declRef (CoreCpp.Ty.int) "y" (CoreCpp.Expr.var "x"))
```

# §10.2 As regras

```tree
Γ ⊢ₗ e : τ    τ tem valores    τ bem formado
───────────────────────────────────────────── (T-DeclRef)
Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]

ρ, σ ⊢ e ⇒ₗ ℓ, σ'
───────────────────────────────────────── (DeclRef)
ρ, σ ⊢ τ& x = e ⇒ normal, ρ[x ↦ ℓ], σ'
```

* O inicializador precisa *denotar uma posição*. Onde `Decl` usa ⇒, `DeclRef` usa ⇒ₗ.

* A referência tem em Γ o tipo do referente. Toda regra posterior trata `y` como trata `x`. Nenhuma regra religa.

# §10.2 Pela referência, pela variável

```lean (name := refRun)
def alias : String :=
  "int main() {
     int x = 1;
     int& y = x;
     y = y + 41;
     return x;
   }"

#eval (parseProgram alias).map run
```
```leanOutput refRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

```lean (name := refLiteral)
#eval (parseProgram "int main() { int& r = 5; return r; }").map check
```
```leanOutput refLiteral
Except.ok (Except.error (CoreCpp.TypeError.notLvalue (CoreCpp.Expr.intLit 5)))
```

# §10.3 Ligações próprias e de referência

* `Block` libera σ' ∖ (ρ' ∖ ρ). Com `{ int& y = x; y = 5; }` o bloco acrescenta `y ↦ ℓ0`, e ℓ0 pertence a `x`, fora.

* Liberar ℓ0 deixaria `x` pendente. Cada ligação registra se a declaração é *dona* da posição ou a toma de *empréstimo*.

* `Block` libera só as posições das ligações próprias de ρ' ∖ ρ. A marca não muda nada na busca.

```tree
    [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ int& y = x; ⇒ normal, [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 1}   (DeclRef)
    [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 1} ⊢ y = 5; ⇒ normal, [x ↦ ℓ0, y ↦ ℓ0], {ℓ0 ↦ 5}   (Assign)
  [x ↦ ℓ0], {ℓ0 ↦ 1} ⊢ { int& y = x; y = 5; } ⇒ normal, [x ↦ ℓ0], {ℓ0 ↦ 5}   (Block)
```

* Primeira construção em que *escopo e tempo de vida* de um nome se separam. A referência tem escopo próprio e o tempo de vida do referente.

# §10.4 Apelidos de campos e elementos

```lean (name := refField)
def refField : String :=
  "class P { public: int a; int b; };
   int main() {
     P* p = new P();
     int& a = p->a;
     a = 7;
     return p->a * 10 + p->b;
   }"

#eval (parseProgram refField).map run
```
```leanOutput refField
Except.ok (Except.ok (CoreCpp.Val.int 70))
```

* Qualquer expressão que denote uma posição inicializa uma referência. Um campo, um elemento de vetor, uma variável ponteiro.

* Um ponteiro é um *valor*, guardado, reatribuível, comparável com `nullptr`. Uma referência é uma *ligação*, fixada na declaração, nunca nula.

# §10.5 O que C++ deixa indefinido

* C++ liga referências a temporários, `const int& r = 5`, admite campos de referência, e deixa uma função devolver referência a uma local, que fica *pendente*.

* Core C++ exclui os três por construção. O inicializador denota posição, campos guardam valores, funções devolvem valores.

* Uma referência nomeia uma posição de um *bloco externo*, viva durante todo o seu escopo, ou de um *objeto*, vivo até o fim do programa.

* Nenhuma regra produz referência a posição liberada. `danglingLocation` nunca vem de uma referência.

* C++ avisa sobre o que não pode acontecer em execução. Core C++ tem duas regras, e o resto não existe.

# Resumo

* Uma *referência* é um segundo nome para uma posição existente, feita por `DeclRef` com o juízo de posição.

* Tem o tipo do referente, lê por `Var`, escreve por `Assign`, e nunca é religada.

* As ligações são *próprias* ou *de referência*, e a saída do bloco libera só as posições próprias.

* Referências alcançam campos, elementos de vetor e variáveis ponteiro.

* Referências pendentes são impossíveis em Core C++, pelas regras, não por um aviso.

Exercícios: veja as [notas de aula](../pt/Aula-10___-Refer___ncias-e-Apelidos/).

```lean -show
end Slides10
```
