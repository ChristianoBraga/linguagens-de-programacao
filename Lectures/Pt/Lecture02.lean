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

#doc (Manual) "Aula 2: Sintaxe" =>

%%%
tag := "aula-2"
%%%

```lean -show
namespace Lecture2
open CoreCpp
```

Esta aula trata a sintaxe de uma linguagem de programação em dois níveis. O nível léxico agrupa os caracteres do texto em tokens, e o nível sintático agrupa os tokens em frases da gramática. A aula apresenta os dois níveis sobre Core C++, mostra a diferença entre sintaxe concreta e sintaxe abstrata, e explica por que a gramática de Core C++ é LL(1) e como um analisador descendente recursivo a reconhece. Os alunos conhecem gramáticas livres de contexto e árvores de derivação da disciplina de Linguagens Formais e Autômatos, e a aula parte daí.

*Esta aula também está disponível como [slides de apresentação](../slides/lecture-2.pt.html).*

# Do Texto aos Tokens

%%%
tag := "lexico"
%%%

Um programa chega ao processador de linguagem como uma sequência de caracteres. A *análise léxica* a transforma em uma sequência de *tokens*, as menores unidades com significado sintático, e descarta espaços, quebras de linha e comentários. Um token tem uma *classe*, como identificador ou literal inteiro, e um *lexema*, o texto que o forma.

Os tokens de Core C++ caem em cinco classes, e a {numref}[tbl-tokens] as descreve.

:::table +header
*
  * Classe
  * Descrição
  * Exemplos
*
  * palavra reservada
  * nomes fixos da linguagem
  * `int`, `while`, `return`, `class`, `std::vector`
*
  * identificador de tipo
  * inicial maiúscula
  * `Pilha`, `Forma`, `T`
*
  * identificador de variável
  * inicial minúscula
  * `x`, `acc`, `fatorial`
*
  * literal inteiro
  * dígitos decimais
  * `0`, `42`, `2147483647`
*
  * operador ou pontuação
  * símbolos de um a três caracteres
  * `+`, `<=`, `->`, `[=]`, `{`, `;`
:::

{tabcap "tbl-tokens"}[As cinco classes de tokens de Core C++.]

A distinção entre identificador de tipo e identificador de variável pela inicial é uma *convenção léxica* de Core C++ que C++ não tem. Ela existe para que o analisador léxico decida, sem contexto, se `<` abre uma lista de argumentos de template ou compara dois valores. Em `Pilha<int>` o `<` segue um identificador de tipo, e em `x < y` segue um identificador de variável. C++ resolve essa ambiguidade com uma tabela de símbolos consultada durante a análise sintática, e Core C++ a resolve no léxico.{fnref}[stdfunction]

O analisador léxico de Core C++ é uma função de `String` em `Array Token`, escrita em Lean como um autômato finito sobre a lista de caracteres. Ele aplica a regra do *maior prefixo*, isto é, em cada posição lê o token mais longo que as regras admitem. Assim `<=` é um token, e não `<` seguido de `=`, e `y2` é um identificador, e não `y` seguido de `2`.

```lean (name := lexTokens)
#eval lex "int x = 10 + y2;"
```
```leanOutput lexTokens
Except.ok #[CoreCpp.Token.kw "int", CoreCpp.Token.varId "x", CoreCpp.Token.sym "=", CoreCpp.Token.intLit 10,
  CoreCpp.Token.sym "+", CoreCpp.Token.varId "y2", CoreCpp.Token.sym ";", CoreCpp.Token.eof]
```

O último token, `eof`, marca o fim da entrada e permite ao analisador sintático saber que não há mais o que ler. Um comentário de linha, de `//` até a quebra de linha, é descartado.

```lean (name := lexComment)
#eval lex "acc = acc * i; // multiplica"
```
```leanOutput lexComment
Except.ok #[CoreCpp.Token.varId "acc", CoreCpp.Token.sym "=", CoreCpp.Token.varId "acc", CoreCpp.Token.sym "*",
  CoreCpp.Token.varId "i", CoreCpp.Token.sym ";", CoreCpp.Token.eof]
```

Um caractere que nenhuma regra admite é um *erro léxico*, o primeiro tipo de erro que um processador de linguagem detecta.

```lean (name := lexError)
#eval lex "x @ 1"
```
```leanOutput lexError
Except.error "unexpected character '@'"
```

:::footnotes

{fnAnchor "stdfunction"}[] Os nomes `std::function` e `std::vector` começam com minúscula, então a convenção os classificaria como identificadores de variável. O analisador léxico os reconhece antes da regra de identificador e os trata como palavras reservadas, um token cada. Pelo mesmo motivo Core C++ não tem o token `>>`, e `Pilha<Pilha<int>>` fecha com dois tokens `>`, o que C++ só passou a aceitar em C++11.

:::

# Gramáticas Livres de Contexto

%%%
tag := "gramaticas"
%%%

Uma *gramática livre de contexto* tem um conjunto de símbolos *terminais*, que aqui são as classes de tokens, um conjunto de símbolos *não terminais*, um não terminal inicial e um conjunto de *produções* da forma `A ::= α`, em que `A` é um não terminal e `α` uma sequência de terminais e não terminais. Uma *derivação* parte do símbolo inicial e substitui, a cada passo, um não terminal pelo lado direito de uma de suas produções, até restar só terminais. A sequência de terminais obtida é uma frase da linguagem, e a *árvore de derivação* registra as substituições feitas.

A disciplina escreve gramáticas em EBNF, a notação de Backus e Naur estendida.{margin}[ISO/IEC 14977:1996, *Extended BNF*.] O asterisco posfixo `X*` repete `X` zero ou mais vezes, a interrogação `X?` torna `X` opcional, parênteses agrupam, a barra separa alternativas e os terminais ficam entre aspas simples. A gramática das expressões aritméticas e relacionais de Core C++ é a seguinte.

```
Expr        ::= OrExpr ( '?' Expr ':' Expr )?
OrExpr      ::= AndExpr ( '||' AndExpr )*
AndExpr     ::= EqExpr ( '&&' EqExpr )*
EqExpr      ::= RelExpr ( ( '==' | '!=' ) RelExpr )*
RelExpr     ::= AddExpr ( ( '<' | '<=' | '>' | '>=' ) AddExpr )*
AddExpr     ::= MulExpr ( ( '+' | '-' ) MulExpr )*
MulExpr     ::= UnaryExpr ( ( '*' | '/' | '%' ) UnaryExpr )*
UnaryExpr   ::= ( '!' | '-' ) UnaryExpr | PostfixExpr
PostfixExpr ::= Primary Args?
Primary     ::= IntLit | 'true' | 'false' | VarId | '(' Expr ')'
Args        ::= '(' ( Expr ( ',' Expr )* )? ')'
```

Cada não terminal corresponde a um nível de *precedência*. O condicional `?:` é o mais fraco, depois vêm a disjunção, a conjunção, a igualdade, a ordem, a soma, o produto e os operadores unários, e os literais, variáveis e parênteses são os mais fortes. Uma expressão como `1 + 2 * 3` é derivada com o produto dentro da soma, porque `AddExpr` só alcança `2 * 3` por meio de `MulExpr`. A árvore de derivação abaixo omite os níveis que passam direto.

```
                AddExpr
          ┌────────┼────────┐
       MulExpr    '+'    MulExpr
          │          ┌──────┼──────┐
       Primary   UnaryExpr '*' UnaryExpr
          │          │             │
         '1'        '2'           '3'
```

A repetição `( '+' MulExpr )*` faz cada operador *associar à esquerda*. Em `a - b - c` a primeira subtração é reduzida antes da segunda, e o resultado é `(a - b) - c`, como em C++. Uma gramática que escrevesse `AddExpr ::= MulExpr '-' AddExpr` associaria à direita e daria `a - (b - c)`, um valor diferente.

Uma gramática é *ambígua* quando alguma frase tem duas árvores de derivação. A gramática clássica `E ::= E '+' E | E '*' E | n` é ambígua, porque `1 + 2 * 3` admite uma árvore com a soma na raiz e outra com o produto na raiz, e as duas dão valores diferentes. A gramática por níveis de precedência elimina a ambiguidade. C++ tem outra ambiguidade conhecida, a do `else` pendente, em que `if (a) if (b) x = 1; else x = 2;` admite duas leituras. Core C++ a elimina pela gramática, com chaves obrigatórias em todo ramo de `if`, `while` e `for`.

# Sintaxe Concreta e Sintaxe Abstrata

%%%
tag := "abstrata"
%%%

A gramática acima é a *sintaxe concreta*, que fixa o texto dos programas, com parênteses, precedência e pontuação. Para dar semântica a um programa, importa só a sua estrutura, e essa estrutura é a *sintaxe abstrata*. Uma *árvore de sintaxe abstrata* tem um nó por construção da linguagem, com as subconstruções como filhos, e não guarda parênteses, nem níveis de precedência, nem ponto e vírgula. A árvore de `1 + 2 * 3` e a de `1 + (2 * 3)` são a mesma.

Em Lean a sintaxe abstrata é um tipo indutivo, um construtor por construção. O tipo das expressões de Core C++ no subconjunto atual é o seguinte.

```
inductive Expr where
  | intLit  (n : Int)
  | boolLit (b : Bool)
  | var     (x : String)
  | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)
  | call    (f : String) (args : List Expr)
```

O analisador sintático lê os tokens e constrói um valor desse tipo. A árvore de `1 + 2 * 3` tem `binop .add` na raiz, o literal 1 à esquerda e o produto à direita.

```lean (name := parsePrec)
#eval parseExpr "1 + 2 * 3"
```
```leanOutput parsePrec
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.add)
  (CoreCpp.Expr.intLit 1)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.mul) (CoreCpp.Expr.intLit 2) (CoreCpp.Expr.intLit 3)))
```

A associatividade à esquerda aparece na árvore de `a - b - c`, com a primeira subtração como filha esquerda da segunda.

```lean (name := parseAssoc)
#eval parseExpr "a - b - c"
```
```leanOutput parseAssoc
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.sub)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.sub) (CoreCpp.Expr.var "a") (CoreCpp.Expr.var "b"))
  (CoreCpp.Expr.var "c"))
```

Os comandos formam o tipo `Cmd`, com um construtor para bloco, `if`, `while`, `for`, `return`, declaração, atribuição e expressão como comando. Um `if` sem `else` tem uma lista vazia como segundo ramo.

```lean (name := parseIf)
#eval parseStatement "if (x > 0) { x = x - 1; }"
```
```leanOutput parseIf
Except.ok (CoreCpp.Cmd.ite
  (CoreCpp.Expr.binop (CoreCpp.BinOp.gt) (CoreCpp.Expr.var "x") (CoreCpp.Expr.intLit 0))
  [CoreCpp.Cmd.assign
     (CoreCpp.Expr.var "x")
     (CoreCpp.Expr.binop (CoreCpp.BinOp.sub) (CoreCpp.Expr.var "x") (CoreCpp.Expr.intLit 1))]
  [])
```

Um programa é uma lista de funções, cada uma com tipo de retorno, nome, parâmetros e corpo.

```lean (name := parseProg)
#eval parseProgram "int main() { return 42; }"
```
```leanOutput parseProg
Except.ok [{ ret := CoreCpp.Ty.int,
   name := "main",
   params := [],
   body := [CoreCpp.Cmd.ret (some (CoreCpp.Expr.intLit 42))] }]
```

# Análise Descendente Recursiva e LL(1)

%%%
tag := "ll1"
%%%

Um *analisador descendente recursivo* tem uma função por não terminal. A função de `AddExpr` chama a de `MulExpr`, e enquanto o próximo token for `+` ou `-` o consome e chama `MulExpr` de novo, construindo a árvore da esquerda para a direita. Para escolher a produção, a função olha o próximo token sem o consumir. Quando um token de antecipação basta para decidir toda escolha, a gramática é *LL(1)*.{margin}[A. V. Aho, M. S. Lam, R. Sethi e J. D. Ullman, *Compilers, Principles, Techniques, and Tools*, 2ª ed., Addison-Wesley, 2006, seção 4.4.]

A condição LL(1) se verifica pelos conjuntos FIRST e FOLLOW da disciplina de Linguagens Formais. Para cada não terminal com mais de uma produção, os conjuntos FIRST dos lados direitos precisam ser disjuntos, e uma produção que pode gerar a palavra vazia não pode ter FIRST em comum com o FOLLOW do não terminal. Duas *fatorações à esquerda* garantem a propriedade em Core C++. Em `Statement`, um token de tipo, como `int`, abre uma declaração, e um identificador de variável, `this`, `(` ou um literal abre uma expressão, então o primeiro token decide. Em `ExprStatement ::= Expr ( '=' Expr )?`, a atribuição e a expressão como comando começam pela mesma expressão, e a gramática as reúne em um só não terminal, deixando a presença de `=` decidir depois de ler a expressão.

A gramática LL(1) tem uma consequência prática. O analisador detecta um erro no primeiro token que nenhuma produção admite e diz o que esperava.

```lean (name := parseError)
#eval parseExpr "1 + * 3"
```
```leanOutput parseError
Except.error "syntax error at token 2 ('*'): expected primary expression"
```

A gramática de Core C++ exige inicializador em toda declaração local, uma decisão que remove da linguagem a leitura de variável não inicializada, indefinida em C++. A ausência do `=` é um erro sintático.

```lean (name := parseInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput parseInit
Except.error "syntax error at token 7 (';'): expected '='"
```

A gramática completa de Core C++, com classes, templates e lambdas, está no [blueprint da linguagem](https://christianobraga.github.io/corecpp/), com as convenções léxicas, as duas fatorações e as funções do analisador que cada não terminal recebe. O subconjunto implementado nesta unidade cobre os tipos básicos, as expressões, os comandos e as funções.

# Exercícios

%%%
tag := "exercicios-2"
%%%

{exercise "exr-lexico"}[] Liste os tokens de `Pilha<int>* p = new Pilha<int>(8);` com a classe de cada um. Diga em que posição a convenção da inicial maiúscula decide a leitura de `<`.

{exercise "exr-derivacao"}[] Desenhe a árvore de derivação de `x < 10 && !fim` pela gramática da {secref}[gramaticas], e depois a sua árvore de sintaxe abstrata. Indique o que a segunda omite.

{exercise "exr-associatividade"}[] Escreva uma gramática de dois não terminais para subtrações que associe à direita, e mostre com `8 - 3 - 2` que ela dá um valor diferente do de C++.

{exercise "exr-first"}[] Calcule os conjuntos FIRST de `Statement` para as alternativas de declaração local e de expressão como comando, com a gramática do blueprint, e verifique que são disjuntos.

{exercise "exr-else-pendente"}[] Mostre as duas árvores de derivação de `if (a) if (b) x = 1; else x = 2;` em uma gramática de `if` sem chaves obrigatórias, e explique como a regra de Core C++ elimina a segunda.

{exercise "exr-parse-lean"}[] Use `parseExpr` e `parseStatement` para descobrir a árvore de sintaxe abstrata de `a ? b : c ? d : e` e de `for (int i = 0; i < n; i = i + 1) { s = s + i; }`, e explique a estrutura de cada uma.

```lean -show
end Lecture2
```
