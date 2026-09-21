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

#doc (Manual) "Aula 24: Inferência de Tipos" =>

%%%
tag := "aula-24"
%%%

```lean -show
namespace Lecture24
open CoreCpp
```

Todo tipo dos programas do curso até aqui foi escrito pelo programador. Esta aula pergunta quanto dessa escrita uma linguagem pode assumir, e responde para dois pontos da escala. Core C++ infere o tipo de uma declaração local a partir do seu inicializador, que é o `auto`, e Haskell infere o tipo de um programa inteiro sem anotação alguma, pelo algoritmo de Hindley e Milner. A aula fecha a UD VI rodando o fragmento inteiro da unidade em um programa.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-24.pt.html).*

# O Que `auto` Faz

%%%
tag := "auto"
%%%

Uma declaração local com `auto` não dá tipo. O verificador de tipos toma o do inicializador e liga a variável a ele.

```
Γ ⊢ e : τ    τ tem valores    τ ≠ nullptr_t
─────────────────────────────────────────── (T-Auto)
Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]
```

A regra é a da {secref}[aula-9], e a UD VI não lhe acrescenta caso algum. Ela já alcança os tipos que a unidade introduziu, porque um ponteiro tem valores e uma instanciação é uma classe como outra qualquer.

```lean (name := autoInst)
def autoInst : String :=
  "template<typename T>
  class Box {
  private:
    T v;
  public:
    Box(T x) { this->v = x; }
    T get() { return v; }
  };
  int main() {
    auto c = new Box<int>(42);
    auto n = c->get();
    delete c;
    return n;
  }"

#eval (parseProgram autoInst).map run
```
```leanOutput autoInst
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

O ganho é na escrita, não na verificação. As duas variáveis têm tipo tão definido quanto se ele tivesse sido escrito, e o programa que corre é o mesmo. O leitor de `auto c = new Box<int>(42)` vê o tipo no inicializador, que é o caso em que `auto` ajuda, e o leitor de `auto n = c->get()` precisa olhar a declaração de `get` para saber que `n` é um `int`, que é o caso em que ele custa.

Duas premissas da regra recusam uma declaração. Um tipo sem valores, `void` ou um tipo de objeto, não pode ser o tipo de uma variável, como as unidades anteriores decidiram, e `nullptr` tem um tipo próprio que não nomeia variável.

```lean (name := autoNull)
#eval (parseProgram "int main() { auto x = nullptr; return 0; }").map check
```
```leanOutput autoNull
Except.ok (Except.error (CoreCpp.TypeError.objectByValue "variable x" (CoreCpp.Ty.nullT)))
```

Um lambda é recusado por outra razão. Ele não tem tipo algum no subconjunto, como a {secref}[aula-15] decidiu, então não há tipo para `auto` copiar, e a gramática mantém um lambda fora de uma declaração com `auto`.

# A Inferência Local e o Seu Limite

%%%
tag := "limite"
%%%

A inferência de `auto` é *local*. Ela olha uma declaração, toma o tipo de uma expressão que já sabe tipar, e não vai além. Ela nunca corre para trás, de um uso para uma declaração, e nunca resolve um tipo desconhecido.

O limite aparece nos parâmetros de uma função. Uma função do subconjunto declara o tipo de cada parâmetro e o do seu resultado, e regra alguma toma qualquer um deles do corpo ou de uma chamada.

```lean (name := autoParam)
#eval parseProgram
  "auto f(auto x) { return x; }
  int main() { return f(1); }"
```
```leanOutput autoParam
Except.error "syntax error at token 0 ('auto'): expected basic type"
```

C++ passou a admitir as duas formas, o parâmetro com `auto` desde C++20, em que ele abrevia um template de função, e o resultado com `auto` desde C++14, em que ele é tomado do `return`. O subconjunto não admite nenhuma, porque a primeira é um template de função e a segunda faria o tipo de uma função depender do seu corpo, que a regra `T-Fun` lê na direção contrária.

# Inferência sobre um Programa Inteiro

%%%
tag := "hindley-milner"
%%%

No outro extremo da escala, uma linguagem pode não pedir tipo algum e achar o mais geral para toda expressão. Haskell faz isso, com o algoritmo de Hindley e Milner.{margin}[R. Milner, *A Theory of Type Polymorphism in Programming*, Journal of Computer and System Sciences 17(3), 1978, pp. 348 a 375.] A definição abaixo não declara nada.

```
comprimento [] = 0
comprimento (x : xs) = 1 + comprimento xs
```

O algoritmo dá a cada desconhecido uma variável de tipo, percorre a definição coletando equações entre tipos, as *restrições*, e as resolve por unificação. A primeira equação diz que o argumento é uma lista, a segunda que o resultado é um número, e nada no corpo diz quais são os elementos, então o tipo do elemento continua uma variável. A resposta é `comprimento :: [a] -> Int`, lida como, para todo tipo `a`, uma função de listas de `a` em inteiros.

A diferença com respeito a um template merece enunciado preciso. A definição em Haskell é *uma* implementação que serve a todo `a`, e o compilador a verificou uma vez, para todo `a` de uma vez, porque o corpo nunca olha um elemento. Uma `Stack<T>` é um texto expandido uma vez por instanciação, e cada expansão é verificada por si. O tipo em Haskell também enuncia o que a função exige, nada neste caso, enquanto o template nada enuncia e deixa a instanciação falhar.

O que o algoritmo compra é que um programa não precisa de anotação e ainda assim tem tipos. O que ele custa é que os tipos que ele acha se limitam a uma disciplina em que uma variável designa um tipo de cada vez, e no momento em que uma linguagem admite subtipagem, sobrecarga ou um parâmetro usado em dois tipos dentro de um corpo, as equações deixam de ter uma única solução mais geral. C++ tem os três, e é por isso que C++ infere localmente e pede ao programador que escreva o resto, e Haskell não tem nenhum deles nessa forma, e é por isso que ele infere tudo. Haskell recupera a sobrecarga por um mecanismo à parte, a classe de tipos, que mantém a restrição no tipo em vez de a resolver na chamada.

A {numref}[tbl-inference] põe os dois extremos e um meio lado a lado.

:::table +header
*
  * Linguagem
  * O que é inferido
  * O que é escrito
*
  * C, Pascal
  * nada
  * todo tipo
*
  * Core C++, C++, Java, Rust
  * o tipo de uma declaração local
  * parâmetros e resultados
*
  * Haskell, OCaml
  * todo tipo
  * nada, e uma anotação é uma conferência
:::

{tabcap "tbl-inference"}[Quanto da tipagem cada linguagem assume.]

# A Unidade em um Programa

%%%
tag := "unidade-inteira"
%%%

O programa abaixo usa toda construção da UD VI. Um template de classe com um membro que devolve referência, de modo que a indexação denota posição. Um operador membro, de modo que um `+` infixo sobre um objeto é uma chamada de método. Duas sobrecargas de um nome de função. E `auto` sobre um ponteiro para uma instanciação.

```lean (name := whole)
def whole : String :=
  "template<typename T>
  class Vect {
  private:
    std::vector<T>* data;
  public:
    Vect(int n) { this->data = new std::vector<T>(n); }
    T& operator[](int i) { return (*data)[i]; }
    ~Vect() { delete data; }
  };
  class Point {
  public:
    int x;
    Point* operator+(Point& o) {
      Point* r = new Point();
      r->x = x + o.x;
      return r;
    }
  };
  int sum(int a) { return a; }
  int sum(int a, int b) { return a + b; }
  int main() {
    auto v = new Vect<int>(2);
    (*v)[0] = 20;
    (*v)[1] = sum(20, 2);
    int s = sum((*v)[0]) + (*v)[1];
    Point* p = new Point();
    p->x = 0;
    Point* q = *p + *p;
    int r = s + q->x;
    delete v;
    delete p;
    delete q;
    return r;
  }"

#eval (parseProgram whole).map check
```
```leanOutput whole
Except.ok (Except.ok ())
```

```lean (name := wholeRun)
#eval (parseProgram whole).map run
```
```leanOutput wholeRun
Except.ok (Except.ok (CoreCpp.Val.int 42))
```

Ler a derivação do mesmo programa mostra para onde foi cada construção. A instanciação não deixou traço, porque aconteceu antes da execução. As chamadas sobrecarregadas aparecem como chamadas comuns, para a função que o verificador escolheu. O operador e a indexação aparecem como chamadas de método.

```lean (name := wholeTrace)
#eval match parseProgram whole with
  | .ok p =>
    IO.println (String.intercalate "\n"
      ((renderTrace (runWith true p).2).splitOn "\n" |>.filter
        fun l =>
          l.endsWith "(MethodLoc)" || l.endsWith "(LocOf)"))
  | .error e => IO.println e
```
```leanOutput wholeTrace
        [this ↦ ℓ1, i ↦ ℓ7], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ7 ↦ 0} ⊢ &(*data)[i] ⇒ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ7 ↦ 0}   (LocOf)
    [v ↦ ℓ6], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1} ⊢ (*v)[0] ⇒ₗ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 0, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1}   (MethodLoc)
        [this ↦ ℓ1, i ↦ ℓ10], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ10 ↦ 1} ⊢ &(*data)[i] ⇒ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ10 ↦ 1}   (LocOf)
    [v ↦ ℓ6], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1} ⊢ (*v)[1] ⇒ₗ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 0, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1}   (MethodLoc)
            [this ↦ ℓ1, i ↦ ℓ11], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ11 ↦ 0} ⊢ &(*data)[i] ⇒ ℓ3, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ11 ↦ 0}   (LocOf)
          [this ↦ ℓ1, i ↦ ℓ13], {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ13 ↦ 1} ⊢ &(*data)[i] ⇒ ℓ4, {ℓ0 ↦ ℓ5, ℓ1 ↦ Vect<int>{data ↦ ℓ0}, ℓ3 ↦ 20, ℓ4 ↦ 22, ℓ5 ↦ vector[ℓ3, ℓ4], ℓ6 ↦ ℓ1, ℓ13 ↦ 1}   (LocOf)
```

A regra `MethodLoc` é a chamada de `operator[]` em posição que pede posição, e `LocOf` é o `return` desse membro, que devolve a posição do elemento em vez do seu valor. Juntas elas são todo o conteúdo da frase "`v[i]` é uma chamada de método que devolve `int&`", que o projeto da linguagem enunciou e que esta unidade tornou verdadeira.

# Exercícios

%%%
tag := "exercicios-24"
%%%

{exercise "exr-auto-where"}[] Tome um programa da UD V de vinte linhas e troque todo tipo local por `auto`. Diga para cada troca se o programa ficou mais fácil ou mais difícil de ler, e por quê.

{exercise "exr-auto-refused"}[] Dê três declarações com `auto` que o verificador de tipos recusa, uma por premissa da regra, e relacione cada mensagem à premissa.

{exercise "exr-hm-length"}[] Rode o algoritmo de Hindley e Milner à mão sobre a definição de `comprimento`, escrevendo as variáveis de tipo e as equações que você coleta, e chegue à resposta.

{exercise "exr-hm-subtyping"}[] Dê um programa com duas classes de uma cadeia e uma função que devolve uma ou outra conforme uma condição. Diga que tipo o algoritmo de Hindley e Milner tentaria achar para ela, e por que a subtipagem atrapalha.

{exercise "exr-whole-unit"}[] Estenda o programa da {secref}[unidade-inteira] com uma segunda instanciação de `Vect` e uma sobrecarga de `sum` sobre ponteiros, rode o verificador de tipos e o interpretador, e diga que linhas da derivação mudaram.

{exercise "exr-unit-summary"}[] Escreva, em uma página, as quatro construções da UD VI com a regra de cada uma, e diga para cada uma se ela custa algo em tempo de execução.

```lean -show
end Lecture24
```
