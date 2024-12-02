/*
 * TinyC compiler written in Go
 * Copyright (C) 2024  Mateja Marić
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package main

import (
	"fmt"
	"strconv"
	"unicode"
)

/*
 * The integer global variables "a" to "z" are predefined and initialized to zero.
 * It is not possible to declare new variables.
 * The compiler reads the program from standard input and prints out the value of the variables that are not zero.
 * The grammar in EBNF is:
 *
 *  <program> ::= <statement>
 *  <statement> ::= "if" <paren_expr> <statement> |
 *                  "if" <paren_expr> <statement> "else" <statement> |
 *                  "while" <paren_expr> <statement> |
 *                  "do" <statement> "while" <paren_expr> ";" |
 *                  "{" { <statement> } "}" |
 *                  <expr> ";" |
 *                  ";"
 *  <paren_expr> ::= "(" <expr> ")"
 *  <expr> ::= <test> | <id> "=" <expr>
 *  <test> ::= <sum> | <sum> "<" <sum>
 *  <sum> ::= <term> | <sum> "+" <term> | <sum> "-" <term>
 *  <term> ::= <id> | <int> | <paren_expr>
 *  <id> ::= "a" | "b" | "c" | "d" | ... | "z"
 *  <int> ::= <an_unsigned_decimal_integer>
 *
 * Examples of the compiler invocations can be found in the `main_test.go` file.
 */

/*---------------------------------------------------------------------------*/
/* Lexer                                                                     */
/*---------------------------------------------------------------------------*/

type SymbolType int

const (
	END SymbolType = iota
	DO_SYM
	ELSE_SYM
	IF_SYM
	WHILE_SYM
	LEFT_BRACKET
	RIGHT_BRACKET
	LEFT_PARN
	RIGHT_PARN
	PLUS
	MINUS
	LESS
	SEMICOLON
	EQUAL
	INTEGER
	VARIABLE
)

func (st SymbolType) String() string {
	return [...]string{
		"END",
		"DO_SYM",
		"ELSE_SYM",
		"IF_SYM",
		"WHILE_SYM",
		"LEFT_BRACKET",
		"RIGHT_BRACKET",
		"LEFT_PARN",
		"RIGHT_PARN",
		"PLUS",
		"MINUS",
		"LESS",
		"SEMICOLON",
		"EQUAL",
		"INTEGER",
		"VARIABLE",
	}[st]
}

type Symbol struct {
	Type  SymbolType
	Value string
}

func (s Symbol) String() string {
	return fmt.Sprintf("%s(%s)", s.Type, s.Value)
}

func extractReservedWord(str string) (*Symbol, bool) {
	reservedWords := map[string]SymbolType{
		"do":    DO_SYM,
		"else":  ELSE_SYM,
		"if":    IF_SYM,
		"while": WHILE_SYM,
	}
	symType, ok := reservedWords[str]
	if !ok {
		return nil, false
	}
	return &Symbol{Type: symType, Value: str}, true
}

func lex(text string) ([]Symbol, error) {
	symbols := []Symbol{}
	consume, peek := strToRuneQueue(text)

	for {
		sym, err := nextSymbol(consume, peek)
		if err != nil {
			return nil, err
		}
		if sym == nil {
			continue
		}
		symbols = append(symbols, *sym)
		if sym.Type == END {
			break
		}
	}

	return symbols, nil
}

func strToRuneQueue(str string) (consume, peek func() (rune, bool)) {
	runeIndex := 0
	runeList := []rune(str)

	consume = func() (rune, bool) {
		if runeIndex > len(runeList)-1 {
			return 0, false
		}
		char := runeList[runeIndex]
		runeIndex++
		return char, true
	}

	peek = func() (rune, bool) {
		if runeIndex > len(runeList)-1 {
			return 0, false
		}
		return runeList[runeIndex], true
	}

	return
}

func nextSymbol(consume, peek func() (rune, bool)) (*Symbol, error) {
	c, ok := consume()
	if !ok {
		return &Symbol{Type: END, Value: ""}, nil
	}

	switch c {
	case ' ':
		return nil, nil
	case '\n':
		return nil, nil
	case '{':
		return &Symbol{Type: LEFT_BRACKET, Value: "{"}, nil
	case '}':
		return &Symbol{Type: RIGHT_BRACKET, Value: "}"}, nil
	case '(':
		return &Symbol{Type: LEFT_PARN, Value: "("}, nil
	case ')':
		return &Symbol{Type: RIGHT_PARN, Value: ")"}, nil
	case '+':
		return &Symbol{Type: PLUS, Value: "+"}, nil
	case '-':
		return &Symbol{Type: MINUS, Value: "-"}, nil
	case '<':
		return &Symbol{Type: LESS, Value: "<"}, nil
	case ';':
		return &Symbol{Type: SEMICOLON, Value: ";"}, nil
	case '=':
		return &Symbol{Type: EQUAL, Value: "="}, nil
	default:
		if unicode.IsDigit(c) {
			return handleInteger(c, consume, peek)
		}
		if unicode.IsLetter(c) {
			return handleLetters(c, consume, peek)
		}
	}

	return nil, fmt.Errorf("Unknown symbol: %v", c)
}

func handleInteger(r rune, consume, peek func() (rune, bool)) (*Symbol, error) {
	currentRune := r
	runeList := make([]rune, 0)

	for unicode.IsDigit(currentRune) {
		runeList = append(runeList, currentRune)

		peekedRune, ok := peek()
		if !ok || !unicode.IsDigit(peekedRune) {
			break
		}

		currentRune, ok = consume()
		if !ok {
			break
		}
	}

	return &Symbol{Type: INTEGER, Value: string(runeList)}, nil
}

func handleLetters(r rune, consume, peek func() (rune, bool)) (*Symbol, error) {
	currentRune := r
	runeList := make([]rune, 0, 5)

	for unicode.IsLetter(currentRune) {
		runeList = append(runeList, currentRune)

		peekedRune, ok := peek()
		if !ok || !unicode.IsLetter(peekedRune) {
			break
		}

		currentRune, ok = consume()
		if !ok {
			break
		}
	}

	if len(runeList) == 1 {
		return &Symbol{Type: VARIABLE, Value: string(runeList)}, nil
	}

	sym, ok := extractReservedWord(string(runeList))
	if !ok {
		return nil, fmt.Errorf("Unknown reserved word: %s", string(runeList))
	}
	return sym, nil
}

/*---------------------------------------------------------------------------*/
/* Parser                                                                    */
/*---------------------------------------------------------------------------*/

type NodeType int

const (
	VAR_NODE NodeType = iota
	CONST
	ADD
	SUB
	LT
	SET
	IF
	IF_ELSE
	WHILE
	DO
	EMPTY
	SEQ
	EXPR
	PROG
)

func (nt NodeType) String() string {
	return [...]string{
		"VAR_NODE",
		"CONST",
		"ADD",
		"SUB",
		"LT",
		"SET",
		"IF",
		"IF_ELSE",
		"WHILE",
		"DO",
		"EMPTY",
		"SEQ",
		"EXPR",
		"PROG",
	}[nt]
}

type Node struct {
	Type       NodeType
	Value      int
	O1, O2, O3 *Node
}

func (n *Node) String() string {
	return fmt.Sprintf("\n(%s(%d)%s %s %s)", n.Type, n.Value, n.O1, n.O2, n.O3)
}

func NewNode(ntype NodeType) *Node {
	return &Node{Type: ntype}
}

func NewNodeV(ntype NodeType, value int) *Node {
	return &Node{ntype, value, nil, nil, nil}
}

func NewNode1(ntype NodeType, o1 *Node) *Node {
	return &Node{ntype, 0, o1, nil, nil}
}

func NewNode2(ntype NodeType, o1, o2 *Node) *Node {
	return &Node{ntype, 0, o1, o2, nil}
}

func NewNode3(ntype NodeType, o1, o2, o3 *Node) *Node {
	return &Node{ntype, 0, o1, o2, o3}
}

type State struct {
	Data   []Symbol
	Offset int
}

func peek(s State) Symbol {
	if s.Offset >= len(s.Data) {
		return Symbol{END, ""}
	}
	return s.Data[s.Offset]
}

func consume(s State) (Symbol, State) {
	sym := peek(s)
	s.Offset++
	return sym, s
}

func symbolQueue(symbols []Symbol) (consume, peek func() (Symbol, bool)) {
	index := 0

	consume = func() (Symbol, bool) {
		if index > len(symbols)-1 {
			return Symbol{END, ""}, false
		}
		char := symbols[index]
		index++
		return char, true
	}

	peek = func() (Symbol, bool) {
		if index > len(symbols)-1 {
			return Symbol{END, ""}, false
		}
		return symbols[index], true
	}

	return
}

func parse(symbols []Symbol) (*Node, error) {
	consume, peek := symbolQueue(symbols)

	astRoot := NewNode(PROG)
	// astRoot.O1 = statement(consume, peek)
	astRoot.O1 = sum(consume, peek)

	if sym, _ := peek(); sym.Type != END {
		return nil, fmt.Errorf("Expected END, got %s", sym)
	}
	return astRoot, nil
}

// <term> ::= <id> | <int> | <paren_expr>
func term(consume, peek func() (Symbol, bool)) *Node {
	var n *Node
	sym, _ := peek()

	if sym.Type == VARIABLE {
		val := int(sym.Value[0] - 'a')
		n = NewNodeV(VAR_NODE, val)
		consume()
	} else if sym.Type == INTEGER {
		val, _ := strconv.Atoi(sym.Value)
		n = NewNodeV(CONST, val)
		consume()
	} else {
		// n = paren_expr(consume, peek)
	}

	return n
}

// <sum> ::= <term> | <sum> "+" <term> | <sum> "-" <term>
// After eliminating left recursion
// <sum> ::= <term> <sum'>
// <sum'> ::= "+" <term> <sum'> | "-" <term> <sum'> | empty
func sum(consume, peek func() (Symbol, bool)) *Node {
	t := term(consume, peek)
	s := sumPrime(consume, peek, t)
	return s
}

func sumPrime(consume, peek func() (Symbol, bool), prev *Node) *Node {
	sym, _ := peek()
	if sym.Type != PLUS && sym.Type != MINUS {
		return prev
	}

	consume()
	t := term(consume, peek)

	var n *Node
	if sym.Type == PLUS {
		n = NewNode2(ADD, prev, t)
	} else {
		n = NewNode2(SUB, prev, t)
	}

	return sumPrime(consume, peek, n)
}

/*---------------------------------------------------------------------------*/
/* Main program                                                              */
/*---------------------------------------------------------------------------*/

func main() {
}
