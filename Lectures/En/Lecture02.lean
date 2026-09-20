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

#doc (Manual) "Lecture 2: Syntax" =>

%%%
tag := "lecture-2"
%%%

```lean -show
namespace Lecture2
open CoreCpp
```

This lecture treats the syntax of a programming language at two levels. The lexical level groups the characters of the text into tokens, and the syntactic level groups the tokens into phrases of the grammar. The lecture presents both levels over Core C++, shows the difference between concrete and abstract syntax, and explains why the grammar of Core C++ is LL(1) and how a recursive descent parser recognises it. Students know context free grammars and derivation trees from the course on formal languages and automata, and the lecture starts there.

*This lecture is also available as [presentation slides](../slides/lecture-2.en.html).*

# From Text to Tokens

%%%
tag := "lexical"
%%%

A program reaches the language processor as a sequence of characters. *Lexical analysis* turns it into a sequence of *tokens*, the smallest units with syntactic meaning, and discards white space, line breaks and comments. A token has a *class*, such as identifier or integer literal, and a *lexeme*, the text that forms it.

The tokens of Core C++ fall into five classes, and {numref}[tbl-tokens] describes them.

:::table +header
*
  * Class
  * Description
  * Examples
*
  * reserved word
  * fixed names of the language
  * `int`, `while`, `return`, `class`, `std::vector`
*
  * type identifier
  * uppercase initial
  * `Pilha`, `Forma`, `T`
*
  * variable identifier
  * lowercase initial
  * `x`, `acc`, `fatorial`
*
  * integer literal
  * decimal digits
  * `0`, `42`, `2147483647`
*
  * operator or punctuation
  * symbols of one to three characters
  * `+`, `<=`, `->`, `[=]`, `{`, `;`
:::

{tabcap "tbl-tokens"}[The five token classes of Core C++.]

The distinction between type identifiers and variable identifiers by their initial is a *lexical convention* of Core C++ that C++ lacks. It exists so that the lexer decides, without context, whether `<` opens a template argument list or compares two values. In `Pilha<int>` the `<` follows a type identifier, and in `x < y` it follows a variable identifier. C++ resolves this ambiguity with a symbol table consulted during parsing, and Core C++ resolves it in the lexer.{fnref}[stdfunction]

The lexer of Core C++ is a function from `String` to `Array Token`, written in Lean as a finite automaton over the list of characters. It applies the *longest match* rule, that is, at each position it reads the longest token the rules admit. Thus `<=` is one token, not `<` followed by `=`, and `y2` is an identifier, not `y` followed by `2`.

```lean (name := lexTokens)
#eval lex "int x = 10 + y2;"
```
```leanOutput lexTokens
Except.ok #[CoreCpp.Token.kw "int", CoreCpp.Token.varId "x", CoreCpp.Token.sym "=", CoreCpp.Token.intLit 10,
  CoreCpp.Token.sym "+", CoreCpp.Token.varId "y2", CoreCpp.Token.sym ";", CoreCpp.Token.eof]
```

The last token, `eof`, marks the end of the input and lets the parser know that there is nothing more to read. A line comment, from `//` to the line break, is discarded.

```lean (name := lexComment)
#eval lex "acc = acc * i; // multiplica"
```
```leanOutput lexComment
Except.ok #[CoreCpp.Token.varId "acc", CoreCpp.Token.sym "=", CoreCpp.Token.varId "acc", CoreCpp.Token.sym "*",
  CoreCpp.Token.varId "i", CoreCpp.Token.sym ";", CoreCpp.Token.eof]
```

A character no rule admits is a *lexical error*, the first kind of error a language processor detects.

```lean (name := lexError)
#eval lex "x @ 1"
```
```leanOutput lexError
Except.error "unexpected character '@'"
```

:::footnotes

{fnAnchor "stdfunction"}[] The names `std::function` and `std::vector` start with a lowercase letter, so the convention would classify them as variable identifiers. The lexer recognises them before the identifier rule and treats them as reserved words, one token each. For the same reason Core C++ has no token `>>`, and `Pilha<Pilha<int>>` closes with two tokens `>`, which C++ only came to accept in C++11.

:::

# Context Free Grammars

%%%
tag := "grammars"
%%%

A *context free grammar* has a set of *terminal* symbols, here the token classes, a set of *nonterminal* symbols, an initial nonterminal and a set of *productions* of the form `A ::= α`, where `A` is a nonterminal and `α` a sequence of terminals and nonterminals. A *derivation* starts from the initial symbol and replaces, at each step, a nonterminal by the right side of one of its productions, until only terminals remain. The sequence of terminals obtained is a phrase of the language, and the *derivation tree* records the replacements made.

The course writes grammars in EBNF, the extended Backus Naur notation.{margin}[ISO/IEC 14977:1996, *Extended BNF*.] The postfix asterisk `X*` repeats `X` zero or more times, the question mark `X?` makes `X` optional, parentheses group, the bar separates alternatives and terminals stand between single quotes. The grammar of the arithmetic and relational expressions of Core C++ follows.

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

Each nonterminal corresponds to a level of *precedence*. The conditional `?:` is the weakest, then come disjunction, conjunction, equality, order, sum, product and the unary operators, and literals, variables and parentheses are the strongest. An expression such as `1 + 2 * 3` is derived with the product inside the sum, because `AddExpr` only reaches `2 * 3` through `MulExpr`. The derivation tree below omits the levels that pass straight through.

```
                AddExpr
          ┌────────┼────────┐
       MulExpr    '+'    MulExpr
          │          ┌──────┼──────┐
       Primary   UnaryExpr '*' UnaryExpr
          │          │             │
         '1'        '2'           '3'
```

The repetition `( '+' MulExpr )*` makes every operator *associate to the left*. In `a - b - c` the first subtraction is reduced before the second, and the result is `(a - b) - c`, as in C++. A grammar that wrote `AddExpr ::= MulExpr '-' AddExpr` would associate to the right and give `a - (b - c)`, a different value.

A grammar is *ambiguous* when some phrase has two derivation trees. The classical grammar `E ::= E '+' E | E '*' E | n` is ambiguous, because `1 + 2 * 3` admits one tree with the sum at the root and another with the product at the root, and the two give different values. The grammar by precedence levels removes the ambiguity. C++ has another well known ambiguity, the dangling `else`, in which `if (a) if (b) x = 1; else x = 2;` admits two readings. Core C++ removes it through the grammar, with mandatory braces in every branch of `if`, `while` and `for`.

# Concrete and Abstract Syntax

%%%
tag := "abstract"
%%%

The grammar above is the *concrete syntax*, which fixes the text of programs, with parentheses, precedence and punctuation. To give a program a semantics, only its structure matters, and that structure is the *abstract syntax*. An *abstract syntax tree* has one node per construction of the language, with the subconstructions as children, and keeps no parentheses, no precedence levels and no semicolons. The tree of `1 + 2 * 3` and that of `1 + (2 * 3)` are the same.

In Lean the abstract syntax is an inductive type, one constructor per construction. The type of the expressions of Core C++ in the current subset follows.

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

The parser reads the tokens and builds a value of this type. The tree of `1 + 2 * 3` has `binop .add` at the root, the literal 1 on the left and the product on the right.

```lean (name := parsePrec)
#eval parseExpr "1 + 2 * 3"
```
```leanOutput parsePrec
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.add)
  (CoreCpp.Expr.intLit 1)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.mul) (CoreCpp.Expr.intLit 2) (CoreCpp.Expr.intLit 3)))
```

Left associativity shows in the tree of `a - b - c`, with the first subtraction as the left child of the second.

```lean (name := parseAssoc)
#eval parseExpr "a - b - c"
```
```leanOutput parseAssoc
Except.ok (CoreCpp.Expr.binop
  (CoreCpp.BinOp.sub)
  (CoreCpp.Expr.binop (CoreCpp.BinOp.sub) (CoreCpp.Expr.var "a") (CoreCpp.Expr.var "b"))
  (CoreCpp.Expr.var "c"))
```

Commands form the type `Cmd`, with one constructor for block, `if`, `while`, `for`, `return`, declaration, assignment and expression statement. An `if` without `else` has an empty list as its second branch.

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

A program is a list of declarations. In this unit every declaration is a function, with a return type, a name, parameters and a body, and Unit II adds classes.

```lean (name := parseProg)
#eval parseProgram "int main() { return 42; }"
```
```leanOutput parseProg
Except.ok [CoreCpp.Decl.fn
   { ret := CoreCpp.Ty.int, name := "main", params := [], body := [CoreCpp.Cmd.ret (some (CoreCpp.Expr.intLit 42))] }]
```

# Recursive Descent Parsing and LL(1)

%%%
tag := "ll1"
%%%

A *recursive descent parser* has one function per nonterminal. The function for `AddExpr` calls the one for `MulExpr`, and while the next token is `+` or `-` it consumes it and calls `MulExpr` again, building the tree from left to right. To choose the production, the function looks at the next token without consuming it. When one token of lookahead suffices for every choice, the grammar is *LL(1)*.{margin}[A. V. Aho, M. S. Lam, R. Sethi and J. D. Ullman, *Compilers, Principles, Techniques, and Tools*, 2nd ed., Addison-Wesley, 2006, section 4.4.]

The LL(1) condition is checked with the FIRST and FOLLOW sets of the course on formal languages. For each nonterminal with more than one production, the FIRST sets of the right sides must be disjoint, and a production that can generate the empty word must not share FIRST with the FOLLOW of the nonterminal. Two *left factorings* guarantee the property in Core C++. In `Statement`, a type token, such as `int`, opens a declaration, and a variable identifier, `this`, `(` or a literal opens an expression, so the first token decides. In `ExprStatement ::= Expr ( '=' Expr )?`, assignment and expression statement start with the same expression, and the grammar joins them in one nonterminal, letting the presence of `=` decide after the expression has been read.

The LL(1) grammar has a practical consequence. The parser detects an error at the first token that no production admits and says what it expected.

```lean (name := parseError)
#eval parseExpr "1 + / 3"
```
```leanOutput parseError
Except.error "syntax error at token 2 ('/'): expected primary expression"
```

The grammar of Core C++ requires an initialiser in every local declaration, a decision that removes from the language the reading of an uninitialised variable, undefined in C++. A missing `=` is a syntax error.

```lean (name := parseInit)
#eval parseProgram "int main() { int x; return x; }"
```
```leanOutput parseInit
Except.error "syntax error at token 7 (';'): expected '='"
```

The complete grammar of Core C++, with classes, templates and lambdas, is in the [blueprint of the language](https://christianobraga.github.io/corecpp/), with the lexical conventions, the two factorings and the parser functions each nonterminal receives. The subset implemented in this unit covers basic types, expressions, commands and functions.

# Exercises

%%%
tag := "exercises-2"
%%%

{exercise "exr-lexical"}[] List the tokens of `Pilha<int>* p = new Pilha<int>(8);` with the class of each. Say at which position the uppercase initial convention decides the reading of `<`.

{exercise "exr-derivation"}[] Draw the derivation tree of `x < 10 && !fim` by the grammar of {secref}[grammars], and then its abstract syntax tree. Point out what the second one omits.

{exercise "exr-associativity"}[] Write a grammar with two nonterminals for subtractions that associates to the right, and show with `8 - 3 - 2` that it gives a value different from that of C++.

{exercise "exr-first"}[] Compute the FIRST sets of `Statement` for the local declaration and the expression statement alternatives, with the grammar of the blueprint, and check that they are disjoint.

{exercise "exr-dangling-else"}[] Show the two derivation trees of `if (a) if (b) x = 1; else x = 2;` in a grammar of `if` without mandatory braces, and explain how the rule of Core C++ removes the second.

{exercise "exr-parse-lean"}[] Use `parseExpr` and `parseStatement` to find the abstract syntax tree of `a ? b : c ? d : e` and of `for (int i = 0; i < n; i = i + 1) { s = s + i; }`, and explain the structure of each.

```lean -show
end Lecture2
```
