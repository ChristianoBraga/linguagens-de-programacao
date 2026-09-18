/-
Slides da Aula 2. Cada seção de nível superior é um slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Sintaxe" =>

Tokens, gramáticas, sintaxe abstrata e análise LL(1)

Christiano Braga · Engenharia de Computação · IME

[↩ Abrir as notas de aula](../pt/Aula-2___-Sintaxe/)

```lean -show
namespace SlidesAula2
open CoreCpp
```

# §2.1 Do texto aos tokens

* A *análise léxica* agrupa caracteres em *tokens* e descarta espaços e comentários.

* Um token tem uma *classe* e um *lexema*.

* Cinco classes em Core C++. Palavras reservadas, identificadores de *tipo* com maiúscula, identificadores de *variável* com minúscula, literais inteiros, operadores e pontuação.

* *Maior prefixo*. Em cada posição, o token mais longo. `<=` é um token, `y2` é um identificador.

# §2.1 A convenção da inicial

* Em `Pilha<int>` o `<` segue um identificador de tipo e abre um argumento de template.

* Em `x < y` o `<` segue um identificador de variável e compara.

* C++ decide com uma tabela de símbolos durante a análise sintática. Core C++ decide *no léxico*.

* `std::function` e `std::vector` são um token cada, e não há o token `>>`.

# §2.1 O analisador léxico em Lean

```lean (name := lexTokens)
#eval lex "int x = 10 + y2;"
```
```leanOutput lexTokens
Except.ok #[CoreCpp.Token.kw "int", CoreCpp.Token.varId "x", CoreCpp.Token.sym "=", CoreCpp.Token.intLit 10,
  CoreCpp.Token.sym "+", CoreCpp.Token.varId "y2", CoreCpp.Token.sym ";", CoreCpp.Token.eof]
```

```lean (name := lexError)
#eval lex "x @ 1"
```
```leanOutput lexError
Except.error "unexpected character '@'"
```

* `eof` marca o fim da entrada. Um caractere que nenhuma regra admite é um *erro léxico*.

# §2.2 Gramáticas livres de contexto

* Terminais, as classes de tokens. Não terminais. Um inicial. Produções `A ::= α`.

* Uma *derivação* substitui não terminais até restarem terminais. A *árvore de derivação* registra as substituições.

* Notação EBNF. `X*` repete, `X?` torna opcional, parênteses agrupam, a barra separa alternativas, terminais entre aspas.

# §2.2 As expressões de Core C++

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
```

* Um não terminal por nível de *precedência*. A repetição `( op X )*` associa à *esquerda*.

# §2.2 Precedência na árvore de derivação

```tree
                AddExpr
          ┌────────┼────────┐
       MulExpr    '+'    MulExpr
          │          ┌──────┼──────┐
       Primary   UnaryExpr '*' UnaryExpr
          │          │             │
         '1'        '2'           '3'
```

* `AddExpr` só alcança `2 * 3` por meio de `MulExpr`, então o produto fica dentro da soma.

* A gramática `E ::= E '+' E | E '*' E | n` é *ambígua*. A gramática por níveis não é.

* O `else` pendente de C++ não existe em Core C++. Chaves obrigatórias.

# §2.3 Sintaxe concreta e sintaxe abstrata

* A *sintaxe concreta* fixa o texto, com parênteses, precedência e pontuação.

* A *sintaxe abstrata* guarda só a estrutura. Um nó por construção, as subconstruções como filhos.

* `1 + 2 * 3` e `1 + (2 * 3)` têm a mesma árvore de sintaxe abstrata.

* Em Lean, um tipo indutivo, um construtor por construção.

```
inductive Expr where
  | intLit  (n : Int)        | boolLit (b : Bool)
  | var     (x : String)     | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)   | call    (f : String) (args : List Expr)
```

# §2.3 O analisador sintático em Lean

```lean (name := parsePrec)
#eval parseExpr "1 + 2 * 3"
```
```leanOutput parsePrec
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.add)
  (CoreCpp.Expr.intLit 1)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.mul) (CoreCpp.Expr.intLit 2) (CoreCpp.Expr.intLit 3)))
```

```lean (name := parseAssoc)
#eval parseExpr "a - b - c"
```
```leanOutput parseAssoc
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.sub)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.sub) (CoreCpp.Expr.var "a") (CoreCpp.Expr.var "b"))
  (CoreCpp.Expr.var "c"))
```

# §2.4 Análise descendente recursiva

* Uma *função por não terminal*. A de `AddExpr` chama a de `MulExpr` e, enquanto o próximo token for `+` ou `-`, o consome e chama de novo.

* A função *olha o próximo token sem o consumir* para escolher a produção.

* Quando um token de antecipação basta para toda escolha, a gramática é *LL(1)*.

* Verificação pelos conjuntos FIRST e FOLLOW de Linguagens Formais.

# §2.4 As duas fatorações de Core C++

* Em `Statement`, um token de *tipo* abre uma declaração, e `VarId`, `this`, `(` ou um literal abre uma expressão. O primeiro token decide.

* Em `ExprStatement ::= Expr ( '=' Expr )?`, a atribuição e a expressão como comando começam pela mesma expressão. A gramática as reúne e a presença de `=` decide depois.

```lean (name := parseError)
#eval parseExpr "1 + * 3"
```
```leanOutput parseError
Except.error "syntax error at token 2 ('*'): expected primary expression"
```

* O erro é detectado no *primeiro token* que nenhuma produção admite.

# §2.4 Uma decisão sintática com efeito semântico

```lean (name := parseInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput parseInit
Except.error "syntax error at token 7 (';'): expected '='"
```

* Toda declaração local tem inicializador, *pela gramática*.

* A leitura de variável não inicializada, indefinida em C++, não existe em Core C++.

# Resumo

* *Tokens* têm classe e lexema, e o léxico usa o maior prefixo. Core C++ distingue tipos de variáveis pela *inicial*.

* Uma *gramática livre de contexto* em EBNF, com um não terminal por nível de precedência, é não ambígua e associa à esquerda.

* A *sintaxe abstrata* guarda só a estrutura, e em Lean é um tipo indutivo.

* Um analisador *descendente recursivo* tem uma função por não terminal, e a gramática *LL(1)* decide cada produção com um token.

* Decisões sintáticas eliminam erros. Chaves obrigatórias e inicializador obrigatório.

Exercícios: veja as [notas de aula](../pt/Aula-2___-Sintaxe/).

```lean -show
end SlidesAula2
```
