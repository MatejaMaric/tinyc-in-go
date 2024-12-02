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
	"unicode/utf8"
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

func (st SymbolType) OneOf(types ...SymbolType) bool {
	for _, t := range types {
		if st == t {
			return true
		}
	}
	return false
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

type LexState struct {
	Data   string
	Offset int
}

func peekRune(s LexState) rune {
	r, _ := utf8.DecodeRuneInString(s.Data[s.Offset:])
	return r
}

func consumeRune(s LexState) (rune, LexState) {
	r, n := utf8.DecodeRuneInString(s.Data[s.Offset:])
	if r != utf8.RuneError {
		s.Offset += n
	}
	return r, s
}

func lex(text string) ([]Symbol, error) {
	var sym *Symbol
	state := LexState{Data: text, Offset: 0}
	var err error

	symbols := []Symbol{}
	for {
		sym, state, err = nextSymbol(state)
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

func nextSymbol(state LexState) (*Symbol, LexState, error) {
	r, state := consumeRune(state)

	switch r {
	case utf8.RuneError:
		return &Symbol{Type: END, Value: ""}, state, nil
	case ' ':
		return nil, state, nil
	case '\n':
		return nil, state, nil
	case '{':
		return &Symbol{Type: LEFT_BRACKET, Value: "{"}, state, nil
	case '}':
		return &Symbol{Type: RIGHT_BRACKET, Value: "}"}, state, nil
	case '(':
		return &Symbol{Type: LEFT_PARN, Value: "("}, state, nil
	case ')':
		return &Symbol{Type: RIGHT_PARN, Value: ")"}, state, nil
	case '+':
		return &Symbol{Type: PLUS, Value: "+"}, state, nil
	case '-':
		return &Symbol{Type: MINUS, Value: "-"}, state, nil
	case '<':
		return &Symbol{Type: LESS, Value: "<"}, state, nil
	case ';':
		return &Symbol{Type: SEMICOLON, Value: ";"}, state, nil
	case '=':
		return &Symbol{Type: EQUAL, Value: "="}, state, nil
	default:
		if unicode.IsDigit(r) {
			return handleInteger(state, r)
		}
		if unicode.IsLetter(r) {
			return handleLetters(state, r)
		}
	}

	return nil, state, fmt.Errorf("Unknown symbol: %v", r)
}

func handleInteger(state LexState, r rune) (*Symbol, LexState, error) {
	currentRune := r
	runeList := make([]rune, 0)

	for unicode.IsDigit(currentRune) {
		runeList = append(runeList, currentRune)

		peekedRune := peekRune(state)
		if !unicode.IsDigit(peekedRune) {
			break
		}

		currentRune, state = consumeRune(state)
		if currentRune == utf8.RuneError {
			break
		}
	}

	return &Symbol{Type: INTEGER, Value: string(runeList)}, state, nil
}

func handleLetters(state LexState, r rune) (*Symbol, LexState, error) {
	currentRune := r
	runeList := make([]rune, 0, 5)

	for unicode.IsLetter(currentRune) {
		runeList = append(runeList, currentRune)

		peekedRune := peekRune(state)
		if !unicode.IsLetter(peekedRune) {
			break
		}

		currentRune, state = consumeRune(state)
		if currentRune == utf8.RuneError {
			break
		}
	}

	if len(runeList) == 1 {
		return &Symbol{Type: VARIABLE, Value: string(runeList)}, state, nil
	}

	sym, ok := extractReservedWord(string(runeList))
	if !ok {
		return nil, state, fmt.Errorf("Unknown reserved word: %s", string(runeList))
	}

	return sym, state, nil
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

type Parser func(State) (*Node, State, error)

func parse(state State) (*Node, State, error) {
	statement, state, err := sum(state)
	if err != nil {
		return nil, state, err
	}

	astRoot := NewNode1(PROG, statement)

	if sym := peek(state); sym.Type != END {
		return astRoot, state, fmt.Errorf("Expected END, got %s", sym)
	}

	return astRoot, state, nil
}

// <term> ::= <id> | <int> | <paren_expr>
func term(state State) (*Node, State, error) {
	sym := peek(state)

	if sym.Type == VARIABLE {
		sym, state = consume(state)
		val := int(sym.Value[0] - 'a')
		return NewNodeV(VAR_NODE, val), state, nil
	}

	if sym.Type == INTEGER {
		sym, state = consume(state)
		val, _ := strconv.Atoi(sym.Value)
		return NewNodeV(CONST, val), state, nil
	}

	if sym.Type == RIGHT_PARN {
		return paren_expr(state)
	}

	return nil, state, fmt.Errorf("Expected VARIABLE, INTEGER or RIGHT_PARN, got %s", sym)
}

// <sum> ::= <term> | <sum> "+" <term> | <sum> "-" <term>
// After eliminating left recursion
// <sum> ::= <term> <sum'>
// <sum'> ::= "+" <term> <sum'> | "-" <term> <sum'> | empty
func sum(state State) (*Node, State, error) {
	t, state, err := term(state)
	if err != nil {
		return nil, state, err
	}

	return sumPrime(state, t)
}

func sumPrime(state State, prev *Node) (*Node, State, error) {
	sym := peek(state)

	if !sym.Type.OneOf(PLUS, MINUS) {
		return prev, state, nil
	}
	sym, state = consume(state)

	t, state, err := term(state)
	if err != nil {
		return nil, state, err
	}

	var n *Node
	if sym.Type == PLUS {
		n = NewNode2(ADD, prev, t)
	} else {
		n = NewNode2(SUB, prev, t)
	}

	return sumPrime(state, n)
}

// <test> ::= <sum> | <sum> "<" <sum>
func test(state State) (*Node, State, error) {
	s1, state, err := sum(state)
	if err != nil {
		return nil, state, err
	}

	sym := peek(state)
	if sym.Type != LESS {
		return s1, state, nil
	}
	sym, state = consume(state)

	s2, state, err := sum(state)
	if err != nil {
		return nil, state, err
	}

	return NewNode2(LT, s1, s2), state, nil
}

// <expr> ::= <test> | <id> "=" <expr>
func expr(state State) (*Node, State, error) {
	t, state, err := test(state)
	if err != nil {
		return nil, state, err
	}

	if t.Type == VAR_NODE && peek(state).Type == EQUAL {
		_, state = consume(state)

		e, state, err := expr(state)
		if err != nil {
			return nil, state, err
		}

		return NewNode2(SET, t, e), state, nil
	}

	return t, state, nil
}

// <paren_expr> ::= "(" <expr> ")"
func paren_expr(state State) (*Node, State, error) {
	if peek(state).Type == LEFT_PARN {
		_, state = consume(state)
	} else {
		return nil, state, fmt.Errorf("Expected LEFT_PARN, got %s", peek(state))
	}

	e, state, err := expr(state)
	if err != nil {
		return nil, state, err
	}

	if peek(state).Type == RIGHT_PARN {
		_, state = consume(state)
	} else {
		return nil, state, fmt.Errorf("Expected RIGHT_PARN, got %s", peek(state))
	}

	return e, state, nil
}

/*---------------------------------------------------------------------------*/
/* Main program                                                              */
/*---------------------------------------------------------------------------*/

func main() {
}
