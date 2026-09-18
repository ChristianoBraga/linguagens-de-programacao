/-
Slides of Lecture 2. Each top level section is a slide.
-/

import VersoManual
import Lectures.Meta.SlideDeck
import CoreCpp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lectures

set_option pp.rawOnError true

#doc (Manual) "Syntax" =>

Tokens, grammars, abstract syntax and LL(1) parsing

Christiano Braga · Computer Engineering · IME

[↩ Open the lecture notes](../en/Lecture-2___-Syntax/)

```lean -show
namespace Slides2
open CoreCpp
```

# §2.1 From text to tokens

* *Lexical analysis* groups characters into *tokens* and discards white space and comments.

* A token has a *class* and a *lexeme*.

* Five classes in Core C++. Reserved words, *type* identifiers with an uppercase initial, *variable* identifiers with a lowercase one, integer literals, operators and punctuation.

* *Longest match*. At each position, the longest token. `<=` is one token, `y2` is an identifier.

# §2.1 The initial convention

* In `Pilha<int>` the `<` follows a type identifier and opens a template argument.

* In `x < y` the `<` follows a variable identifier and compares.

* C++ decides with a symbol table during parsing. Core C++ decides *in the lexer*.

* `std::function` and `std::vector` are one token each, and there is no token `>>`.

# §2.1 The lexer in Lean

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

* `eof` marks the end of the input. A character no rule admits is a *lexical error*.

# §2.2 Context free grammars

* Terminals, the token classes. Nonterminals. An initial one. Productions `A ::= α`.

* A *derivation* replaces nonterminals until only terminals remain. The *derivation tree* records the replacements.

* EBNF notation. `X*` repeats, `X?` makes optional, parentheses group, the bar separates alternatives, terminals between quotes.

# §2.2 The expressions of Core C++

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

* One nonterminal per level of *precedence*. The repetition `( op X )*` associates to the *left*.

# §2.2 Precedence in the derivation tree

```tree
                AddExpr
          ┌────────┼────────┐
       MulExpr    '+'    MulExpr
          │          ┌──────┼──────┐
       Primary   UnaryExpr '*' UnaryExpr
          │          │             │
         '1'        '2'           '3'
```

* `AddExpr` only reaches `2 * 3` through `MulExpr`, so the product stays inside the sum.

* The grammar `E ::= E '+' E | E '*' E | n` is *ambiguous*. The grammar by levels is not.

* The dangling `else` of C++ does not exist in Core C++. Mandatory braces.

# §2.3 Concrete and abstract syntax

* The *concrete syntax* fixes the text, with parentheses, precedence and punctuation.

* The *abstract syntax* keeps only the structure. One node per construction, the subconstructions as children.

* `1 + 2 * 3` and `1 + (2 * 3)` have the same abstract syntax tree.

* In Lean, an inductive type, one constructor per construction.

```
inductive Expr where
  | intLit  (n : Int)        | boolLit (b : Bool)
  | var     (x : String)     | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)   | call    (f : String) (args : List Expr)
```

# §2.3 The parser in Lean

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

# §2.4 Recursive descent parsing

* *One function per nonterminal*. The one for `AddExpr` calls the one for `MulExpr` and, while the next token is `+` or `-`, consumes it and calls again.

* The function *looks at the next token without consuming it* to choose the production.

* When one token of lookahead suffices for every choice, the grammar is *LL(1)*.

* Checked with the FIRST and FOLLOW sets of the formal languages course.

# §2.4 The two factorings of Core C++

* In `Statement`, a *type* token opens a declaration, and `VarId`, `this`, `(` or a literal opens an expression. The first token decides.

* In `ExprStatement ::= Expr ( '=' Expr )?`, assignment and expression statement start with the same expression. The grammar joins them and the presence of `=` decides afterwards.

```lean (name := parseError)
#eval parseExpr "1 + * 3"
```
```leanOutput parseError
Except.error "syntax error at token 2 ('*'): expected primary expression"
```

* The error is detected at the *first token* no production admits.

# §2.4 A syntactic decision with a semantic effect

```lean (name := parseInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput parseInit
Except.error "syntax error at token 7 (';'): expected '='"
```

* Every local declaration has an initialiser, *by the grammar*.

* Reading an uninitialised variable, undefined in C++, does not exist in Core C++.

# Summary

* *Tokens* have a class and a lexeme, and the lexer uses the longest match. Core C++ tells types from variables by the *initial*.

* A *context free grammar* in EBNF, with one nonterminal per precedence level, is unambiguous and associates to the left.

* The *abstract syntax* keeps only the structure, and in Lean it is an inductive type.

* A *recursive descent* parser has one function per nonterminal, and an *LL(1)* grammar decides every production with one token.

* Syntactic decisions remove errors. Mandatory braces and mandatory initialiser.

Exercises: see the [lecture notes](../en/Lecture-2___-Syntax/).

```lean -show
end Slides2
```
