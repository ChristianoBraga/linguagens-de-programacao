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

#doc (Manual) "Aula 10: Referências e Apelidos" =>

%%%
tag := "aula-10"
%%%

```lean -show
namespace Lecture10
open CoreCpp
```

Esta aula acrescenta uma construção a Core C++, a referência local `τ& y = e`, e a usa para estudar o *aliasing*, a situação em que dois nomes denotam uma posição. Ela dá à referência as suas regras de tipos e de avaliação, mostra por que o ambiente precisa lembrar quais ligações alocaram a sua posição, segue uma referência a um campo e a um elemento de vetor, e fecha com o que C++ deixa indefinido sobre referências e como Core C++ o exclui por construção.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-10.pt.html).*

# Um Segundo Nome para uma Posição

%%%
tag := "segundo-nome"
%%%

Uma *referência* é um nome para uma posição que já existe. A declaração `int& y = x` não aloca. Ela procura a posição de `x` e liga `y` a ela, de modo que dali em diante `x` e `y` são dois nomes para uma variável. Uma escrita por qualquer dos nomes é vista pelo outro, porque há uma posição e um valor.

A construção acrescenta uma produção à gramática das declarações locais e um construtor à sintaxe abstrata.

```
LocalDecl ::= 'auto' VarId '=' Expr
            | Type '&'? VarId '=' Expr
```

O `&` segue o tipo, e a gramática continua LL(1) porque depois de `Type` o token seguinte é `&` ou um identificador de variável. Não há `auto&` nem campo de referência em classe, ambos possíveis em C++, nem parâmetro por referência ainda, que a UD IV acrescenta.

```lean (name := parseRef)
#eval parseStatement "int& y = x;"
```
```leanOutput parseRef
Except.ok (CoreCpp.Cmd.declRef (CoreCpp.Ty.int) "y" (CoreCpp.Expr.var "x"))
```

# As Regras da Referência

%%%
tag := "regras"
%%%

A regra de tipos exige que o inicializador denote uma posição, pelo juízo Γ ⊢ₗ e : τ da {secref}[aula-6], e tenha exatamente o tipo declarado. A referência entra em Γ com o tipo do seu referente, e não com um tipo próprio, porque toda regra posterior trata `y` como trata `x`. Ler `y` é `Var`, escrever em `y` é `Assign`, e nenhuma regra religa uma referência.

```
Γ ⊢ₗ e : τ    τ tem valores    τ bem formado
───────────────────────────────────────────── (T-DeclRef)
Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]
```

A regra de avaliação usa o juízo de posição em lugar do juízo de avaliação. Onde `Decl` avalia o inicializador para um valor e aloca, `DeclRef` o avalia para uma posição e liga.

```
ρ, σ ⊢ e ⇒ₗ ℓ, σ'
───────────────────────────────────────── (DeclRef)
ρ, σ ⊢ τ& x = e ⇒ normal, ρ[x ↦ ℓ], σ'
```

O programa abaixo escreve pela referência e lê pela variável.

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

Dois programas que o verificador de tipos rejeita. Um literal não denota posição, então não pode inicializar uma referência, e o referente precisa ter o tipo declarado, sem as conversões que a declaração por valor admite.

```lean (name := refLiteral)
#eval (parseProgram "int main() { int& r = 5; return r; }").map check
```
```leanOutput refLiteral
Except.ok (Except.error (CoreCpp.TypeError.notLvalue (CoreCpp.Expr.intLit 5)))
```

```lean (name := refType)
#eval (parseProgram "int main() { int x = 1; bool& b = x; return 0; }").map check
```
```leanOutput refType
Except.ok (Except.error (CoreCpp.TypeError.mismatch "referent of b" (CoreCpp.Ty.bool) (CoreCpp.Ty.int)))
```

# Ligações Próprias e de Referência

%%%
tag := "proprias"
%%%

A regra `Block` da {secref}[aula-3] retira de σ as posições das ligações que o bloco acrescentou, escrito σ' ∖ (ρ' ∖ ρ). Com referências essa leitura está errada. No programa abaixo o bloco interno acrescenta a ligação `y ↦ ℓ0`, e ℓ0 é a posição de `x`, declarada fora. Retirar ℓ0 na chave de fechamento deixaria `x` pendente.

```lean (name := refScope)
def refScope : String :=
  "int main() {
     int x = 1;
     { int& y = x; y = 5; }
     return x;
   }"

#eval match parseProgram refScope with
  | .ok p => IO.println (renderTrace (runWith true p).2)
  | .error e => IO.println e
```
```leanOutput refScope
ρ₀ = []                    σ₀ = {}
ρ₁ = [x ↦ ℓ0]              σ₁ = {ℓ0 ↦ 1}
ρ₂ = [x ↦ ℓ0, y ↦ ℓ0]      σ₂ = {ℓ0 ↦ 5}

                   𝒟₃                                            𝒟₄                                           𝒟₅
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ { int& y = x; y = 5; } ⇒ normal, ρ₁, σ₂    ρ₁, σ₂ ⊢ return x; ⇒ ret 5, ρ₁, σ₂
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 5, σ₀

𝒟₁
  ──────────────────── (LocVar)
  ρ₁, σ₁ ⊢ x ⇒ₗ ℓ0, σ₁
  ───────────────────────────────────── (DeclRef)
  ρ₁, σ₁ ⊢ int& y = x; ⇒ normal, ρ₂, σ₁

𝒟₂
  ────────────────── (Lit)    ──────────────────── (LocVar)
  ρ₂, σ₁ ⊢ 5 ⇒ 5, σ₁          ρ₂, σ₁ ⊢ y ⇒ₗ ℓ0, σ₁
  ───────────────────────────────────────────────────────── (Assign)
  ρ₂, σ₁ ⊢ y = 5; ⇒ normal, ρ₂, σ₂

𝒟₃
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 1 ⇒ 1, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁

𝒟₄
                   𝒟₁                                     𝒟₂
  ρ₁, σ₁ ⊢ int& y = x; ⇒ normal, ρ₂, σ₁    ρ₂, σ₁ ⊢ y = 5; ⇒ normal, ρ₂, σ₂
  ───────────────────────────────────────────────────────────────────────── (Block)
  ρ₁, σ₁ ⊢ { int& y = x; y = 5; } ⇒ normal, ρ₁, σ₂

𝒟₅
  ──────────────────── (LocVar)
  ρ₁, σ₂ ⊢ x ⇒ₗ ℓ0, σ₂
  ───────────────────────────── (Var)
  ρ₁, σ₂ ⊢ x ⇒ 5, σ₂
  ─────────────────────────────────── (Return)
  ρ₁, σ₂ ⊢ return x; ⇒ ret 5, ρ₁, σ₂
```

O bloco termina com a memória ainda guardando ℓ0, agora com o valor 5. Para obter isso, cada ligação de ρ registra se a declaração que a fez é *dona* da posição, como `Decl`, ou a toma de *empréstimo*, como `DeclRef`. A regra `Block` lê ρ' ∖ ρ como as ligações próprias que o bloco acrescentou, e libera só as posições delas. O ambiente impresso na árvore não mostra a marca, porque ela não muda nada na busca, só na saída do bloco.{fnref}[alternativa]

A referência tem um escopo próprio, o bloco que a declara, e compartilha o tempo de vida do seu referente. É a primeira construção em que escopo e tempo de vida de um nome se separam, e a separação entre ρ e σ da {secref}[aula-9] é o que a torna expressável com uma regra nova.

:::footnotes

{fnAnchor "alternativa"}[] Uma leitura mais simples, liberar as posições que não estavam no domínio de σ quando o bloco começou, falha para uma referência a um campo de um objeto criado dentro do bloco. O objeto pode escapar por um ponteiro guardado fora, e a posição do seu campo, alocada no bloco, precisa sobreviver. Só a marca de posse distingue a posição da variável `p` da posição do campo `p->a` que a referência `r` toma de empréstimo.

:::

# Apelidos de Campos e Elementos

%%%
tag := "campos-10"
%%%

O inicializador de uma referência é qualquer expressão que denote uma posição, então uma referência pode nomear um campo de um objeto ou um elemento de um vetor. O juízo de posição da {secref}[aula-6] e da {secref}[aula-7] dá a posição, e a escrita pela referência é vista pelo objeto.

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

Uma referência a uma variável ponteiro também é uma referência, de tipo `P*`. Atribuir por ela muda qual objeto a variável ponteiro nomeia, e o objeto criado pela referência é alcançado pela variável.

```
class P { public: int a; };
int main() {
  P* p = nullptr;
  P*& q = p;
  q = new P();
  q->a = 3;
  return p->a;
}
```

O programa devolve 3, e o exemplo `reference_pointer.cpp` do repositório compila com `g++` para o mesmo código de saída. Ponteiros e referências são duas maneiras de alcançar uma posição. Um ponteiro é um valor, guardado em uma posição própria, que pode ser reatribuído e comparado com `nullptr`. Uma referência é uma ligação, não um valor, fixada na declaração e nunca nula.

# O que C++ Deixa Indefinido

%%%
tag := "indefinido"
%%%

C++ admite referências que Core C++ não admite. Uma referência pode ser ligada a um temporário, `const int& r = 5`, e a linguagem estende a vida do temporário à vida da referência. Uma referência pode ser campo de uma classe, e uma função pode devolver uma referência a uma variável local, destruída no retorno, então a referência fica pendente e qualquer uso dela é comportamento indefinido.

Core C++ exclui os três casos por construção. O inicializador precisa denotar uma posição, então não há temporário. Um campo guarda um valor, então não há campo de referência. Uma função devolve um valor, e a referência é uma declaração local cujo escopo termina com o seu bloco, então uma referência nomeia só uma posição de um bloco externo, viva durante todo o escopo da referência, ou uma posição dentro de um objeto, que vive até o fim do programa nesta unidade. Não há regra sob a qual uma referência nomeie uma posição liberada, e o `erro` `danglingLocation`, que o interpretador reporta para qualquer acesso fora de σ, nunca é produzido por uma referência.

A comparação resume o método da disciplina. C++ descreve a referência pelo que o programador pode escrever e avisa sobre o que não pode acontecer em execução. Core C++ a descreve por duas regras, `T-DeclRef` e `DeclRef`, e as situações que as regras não produzem não existem.

# Exercícios

%%%
tag := "exercicios-10"
%%%

{exercise "exr-derivacao-apelido"}[] Construa no papel a derivação de `int x = 1; int& y = x; int& z = y; z = 9; return x;` e diga quantas posições a memória guarda ao fim.

{exercise "exr-sem-religacao"}[] Em C++ como em Core C++, `y = x` com `y` referência atribui ao referente e não religa `y`. Escreva uma regra `Rebind` que religaria uma referência, diga que juízo ela precisa na premissa, e dê um programa cujo resultado muda sob ela.

{exercise "exr-marca-posse"}[] Dê um programa em que a leitura de `Block` sem a marca de posse, liberar toda posição de ρ' ∖ ρ, produz `danglingLocation`, e um segundo programa em que a leitura que libera as posições ausentes de σ na entrada do bloco o produz. Explique os dois pelas regras.

{exercise "exr-referencia-elemento"}[] Declare uma referência a um elemento de um vetor, escreva por ela e leia o elemento. Depois explique por que uma referência a `(*v)[i]` com `i` fora dos limites é `erro` na declaração e não no primeiro uso.

{exercise "exr-ponteiro-referencia"}[] Liste três diferenças entre um ponteiro e uma referência em Core C++ e nomeie, para cada uma, a regra que a estabelece.

{exercise "exr-cpp-pendente"}[] Escreva um programa C++ com uma função que devolve uma referência a uma variável local, e explique, com as regras de Core C++, que regra teria de existir para o programa estar no subconjunto e por que a disciplina não a acrescenta.

```lean -show
end Lecture10
```
