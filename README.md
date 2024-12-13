### About:

A Go implementation of Marc Feeley's TinyC "compiler" (bytecode interpreter) from 2001.

The are considerable differences between [the original Marc Feeley's implementation](https://www.iro.umontreal.ca/~felipe/IFT2030-Automne2002/Complements/tinyc.c) and this one:
1. The original has ~300loc, while this one has ~750loc.
Although, just by applying different formatting to the original, it would probably double it's loc count.
1. The original implementation heavily relied on global variables, this one does not.
In this implementation the lexer, the parser, the code generator and the virtual machine are implemented as pure functions.
1. This implementation has unit tests with coverage of ~93%.

### How to use:

The integer global variables "a" to "z" are predefined and initialized to zero.
It is not possible to declare new variables.
The compiler reads the program from standard input and prints out the value of the variables that are not zero.
The grammar in EBNF is:

```
<program> ::= <statement>
<statement> ::= "if" <paren_expr> <statement> |
                "if" <paren_expr> <statement> "else" <statement> |
                "while" <paren_expr> <statement> |
                "do" <statement> "while" <paren_expr> ";" |
                "{" { <statement> } "}" |
                <expr> ";" |
                ";"
<paren_expr> ::= "(" <expr> ")"
<expr> ::= <test> | <id> "=" <expr>
<test> ::= <sum> | <sum> "<" <sum>
<sum> ::= <term> | <sum> "+" <term> | <sum> "-" <term>
<term> ::= <id> | <int> | <paren_expr>
<id> ::= "a" | "b" | "c" | "d" | ... | "z"
<int> ::= <an_unsigned_decimal_integer>
```

#### Example:

```bash
go build
echo "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }" | ./tinyc-in-go
```

Output:
```
i = 25
j = 25
```

Additional examples of the compiler invocations can be found in the `main_test.go` file.

### To do:

- While making this implementation, I tried to follow the principles of functional programming (no variables or loops, only constants and functions).
I'm probably going to make a new implementation (on a different branch) using parser combinators, and make this code even more purely functional. 
Parser combinators would replace the current state machine lexer and recursive descent parser.
- I'm probably going to refactor the virtual machine implementation (make it more functional).
