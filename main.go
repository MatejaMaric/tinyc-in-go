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
	"io"
	"os"
	"slices"
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

	return nil, state, fmt.Errorf("Unknown symbol: %c", r)
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
	SEQUENCE
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

func (nt NodeType) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf("\"%s\"", nt.String())), nil
}

type Node struct {
	Type       NodeType
	Value      int64
	O1, O2, O3 *Node
}

func (n *Node) String() string {
	return fmt.Sprintf("\n(%s(%d)%s %s %s)", n.Type, n.Value, n.O1, n.O2, n.O3)
}

func NewNode(ntype NodeType) *Node {
	return &Node{Type: ntype}
}

func NewNodeV(ntype NodeType, value int64) *Node {
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
	statement, state, err := statement(state)
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
		val := int64(sym.Value[0] - 'a')
		return NewNodeV(VAR_NODE, val), state, nil
	}

	if sym.Type == INTEGER {
		sym, state = consume(state)
		val, _ := strconv.ParseInt(sym.Value, 10, 64)
		return NewNodeV(CONST, val), state, nil
	}

	if sym.Type == LEFT_PARN {
		return paren_expr(state)
	}

	return nil, state, fmt.Errorf("Expected VARIABLE, INTEGER or LEFT_PARN, got %s", sym)
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

/*
 *  <program> ::= <statement>
 *  <statement> ::= "if" <paren_expr> <statement> |
 *                  "if" <paren_expr> <statement> "else" <statement> |
 *                  "while" <paren_expr> <statement> |
 *                  "do" <statement> "while" <paren_expr> ";" |
 *                  "{" { <statement> } "}" |
 *                  <expr> ";" |
 *                  ";"
 */
func statement(state State) (*Node, State, error) {
	sym := peek(state)

	// "if" <paren_expr> <statement>
	if sym.Type == IF_SYM {
		sym, state = consume(state)

		pe, state, err := paren_expr(state)
		if err != nil {
			return nil, state, err
		}
		s1, state, err := statement(state)
		if err != nil {
			return nil, state, err
		}

		if peek(state).Type != ELSE_SYM {
			return NewNode2(IF, pe, s1), state, nil
		}

		// ... "else" <statement>
		sym, state = consume(state)
		s2, state, err := statement(state)
		if err != nil {
			return nil, state, err
		}

		return NewNode3(IF_ELSE, pe, s1, s2), state, nil
	}

	// "while" <paren_expr> <statement>
	if sym.Type == WHILE_SYM {
		sym, state = consume(state)

		pe, state, err := paren_expr(state)
		if err != nil {
			return nil, state, err
		}

		s1, state, err := statement(state)
		if err != nil {
			return nil, state, err
		}

		return NewNode2(WHILE, pe, s1), state, nil
	}

	// "do" <statement> "while" <paren_expr> ";"
	if sym.Type == DO_SYM {
		sym, state = consume(state)

		s1, state, err := statement(state)
		if err != nil {
			return nil, state, err
		}

		if peek(state).Type == WHILE_SYM {
			sym, state = consume(state)
		} else {
			return nil, state, fmt.Errorf("Expected WHILE_SYM, got %s", peek(state))
		}

		pe, state, err := paren_expr(state)
		if err != nil {
			return nil, state, err
		}

		if peek(state).Type == SEMICOLON {
			sym, state = consume(state)
		} else {
			return nil, state, fmt.Errorf("Expected SEMICOLON, got %s", peek(state))
		}

		return NewNode2(DO, s1, pe), state, nil
	}

	// ";"
	if sym.Type == SEMICOLON {
		sym, state = consume(state)
		return NewNode(EMPTY), state, nil
	}

	// "{" { <statement> } "}"
	if sym.Type == LEFT_BRACKET {
		_, state = consume(state)
		res, state, err := statement_sequence(state, NewNode(EMPTY))
		if err != nil {
			return nil, state, err
		}
		_, state = consume(state)

		return res, state, nil
	}

	// <expr> ";"
	e, state, err := expr(state)
	if err != nil {
		return nil, state, err
	}

	if peek(state).Type == SEMICOLON {
		sym, state = consume(state)
	} else {
		return nil, state, fmt.Errorf("Expected SEMICOLON, got %s", peek(state))
	}

	return NewNode1(EXPR, e), state, nil
}

func statement_sequence(state State, prev *Node) (*Node, State, error) {
	if peek(state).Type == RIGHT_BRACKET {
		return prev, state, nil
	}

	s, state, err := statement(state)
	if err != nil {
		return nil, state, err
	}

	return statement_sequence(state, NewNode2(SEQUENCE, prev, s))
}

/*---------------------------------------------------------------------------*/
/* Code generator                                                            */
/*---------------------------------------------------------------------------*/

type InstructionType int64

const (
	IFETCH InstructionType = iota
	ISTORE
	IPUSH
	IPOP
	IADD
	ISUB
	ILT
	JZ
	JNZ
	JMP
	HALT
)

func (i InstructionType) String() string {
	strs := [...]string{
		"IFETCH",
		"ISTORE",
		"IPUSH",
		"IPOP",
		"IADD",
		"ISUB",
		"ILT",
		"JZ",
		"JNZ",
		"JMP",
		"HALT",
	}
	if i < 0 || i >= InstructionType(len(strs)) {
		return fmt.Sprintf("UNKNOWN(%d)", i)
	}
	return strs[i]
}

type Instruction struct {
	Value   int64
	IsValue bool
}

func (i Instruction) String() string {
	if i.IsValue {
		return fmt.Sprintf("%d", i.Value)
	}
	return InstructionType(i.Value).String()
}

func NewInst(i InstructionType) Instruction {
	return Instruction{Value: int64(i), IsValue: false}
}

func NewValueInst(i int64) Instruction {
	return Instruction{Value: i, IsValue: true}
}

func NewInstArr(types ...InstructionType) []Instruction {
	instructions := make([]Instruction, 0, len(types))
	for _, t := range types {
		instructions = append(instructions, NewInst(t))
	}
	return instructions
}

func NewValueInstArr(values ...int64) []Instruction {
	instructions := make([]Instruction, 0, len(values))
	for _, t := range values {
		instructions = append(instructions, NewValueInst(t))
	}
	return instructions
}

func convert(ast *Node) []Instruction {
	switch ast.Type {
	case VAR_NODE:
		return []Instruction{NewInst(IFETCH), NewValueInst(ast.Value)}
	case CONST:
		return []Instruction{NewInst(IPUSH), NewValueInst(ast.Value)}
	case ADD:
		return slices.Concat(convert(ast.O1), convert(ast.O2), NewInstArr(IADD))
	case SUB:
		return slices.Concat(convert(ast.O1), convert(ast.O2), NewInstArr(ISUB))
	case LT:
		return slices.Concat(convert(ast.O1), convert(ast.O2), NewInstArr(ILT))
	case SET:
		return slices.Concat(convert(ast.O2), NewInstArr(ISTORE), NewValueInstArr(ast.O1.Value))
	case IF:
		cond := convert(ast.O1)
		s1 := convert(ast.O2)
		s1SkipLength := int64(1 + len(s1))
		return slices.Concat(
			cond,
			[]Instruction{NewInst(JZ), NewValueInst(s1SkipLength)},
			s1,
		)
	case IF_ELSE:
		cond := convert(ast.O1)
		s1 := convert(ast.O2)
		s2 := convert(ast.O3)
		s1SkipLength := int64(1 + len(s1) + len([]Instruction{NewInst(JMP), NewValueInst(0)}))
		s2SkipLength := int64(1 + len(s2))
		return slices.Concat(
			cond,
			[]Instruction{NewInst(JZ), NewValueInst(s1SkipLength)},
			s1,
			[]Instruction{NewInst(JMP), NewValueInst(s2SkipLength)},
			s2,
		)
	case WHILE:
		cond := convert(ast.O1)
		s1 := convert(ast.O2)
		s1SkipLength := int64(1 + len(s1) + len([]Instruction{NewInst(JMP), NewValueInst(0)}))
		backtrackLength := -(int64(len(cond)) + s1SkipLength)
		return slices.Concat(
			cond,
			[]Instruction{NewInst(JZ), NewValueInst(s1SkipLength)},
			s1,
			[]Instruction{NewInst(JMP), NewValueInst(backtrackLength)},
		)
	case DO:
		s1 := convert(ast.O1)
		cond := convert(ast.O2)
		backtrackLength := int64(-(len(s1) + len(cond) + len([]Instruction{NewInst(JNZ)})))
		return slices.Concat(
			s1,
			cond,
			[]Instruction{NewInst(JNZ), NewValueInst(backtrackLength)},
		)
	case EMPTY:
		return []Instruction{}
	case SEQUENCE:
		return slices.Concat(convert(ast.O1), convert(ast.O2))
	case EXPR:
		return slices.Concat(convert(ast.O1), NewInstArr(IPOP))
	case PROG:
		return slices.Concat(convert(ast.O1), NewInstArr(HALT))
	}
	return []Instruction{}
}

/*---------------------------------------------------------------------------*/
/* Virtual machine                                                           */
/*---------------------------------------------------------------------------*/

type Stack []int64

func (s *Stack) Push(v int64) {
	*s = append(*s, v)
}

func (s *Stack) Pop() int64 {
	if len(*s) == 0 {
		panic("virtual machine tried to pop from an empty stack")
	}
	v := (*s)[len(*s)-1]
	*s = (*s)[:len(*s)-1]
	return v
}

func (s *Stack) Peek() int64 {
	if len(*s) == 0 {
		panic("virtual machine tried to peek from an empty stack")
	}
	return (*s)[len(*s)-1]
}

func run(program []Instruction) [26]int64 {
	globals := [26]int64{}
	stack := make(Stack, 1000)
	var pc int64 = 0
	for running := true; running; {
		opcode := program[pc]
		if opcode.IsValue {
			panic(fmt.Sprintf("expected instruction, got value: %d", opcode.Value))
		}
		pc++
		switch InstructionType(opcode.Value) {
		case IFETCH:
			stack.Push(globals[program[pc].Value])
			pc++
		case ISTORE:
			globals[program[pc].Value] = stack.Peek()
			pc++
		case IPUSH:
			stack.Push(program[pc].Value)
			pc++
		case IPOP:
			stack.Pop()
		case IADD:
			b := stack.Pop()
			a := stack.Pop()
			stack.Push(a + b)
		case ISUB:
			b := stack.Pop()
			a := stack.Pop()
			stack.Push(a - b)
		case ILT:
			b := stack.Pop()
			a := stack.Pop()
			if a < b {
				stack.Push(1)
			} else {
				stack.Push(0)
			}
		case JMP:
			pc += program[pc].Value
		case JZ:
			if stack.Pop() == 0 {
				pc += program[pc].Value
			} else {
				pc++
			}
		case JNZ:
			if stack.Pop() != 0 {
				pc += program[pc].Value
			} else {
				pc++
			}
		case HALT:
			running = false
		}
	}

	return globals
}

/*---------------------------------------------------------------------------*/
/* Main program                                                              */
/*---------------------------------------------------------------------------*/

func ReadAndExecute(r io.Reader) string {
	input, err := io.ReadAll(r)
	if err != nil {
		return fmt.Sprintf("Error reading from stdin: %v\n", err)
	}

	symbols, err := lex(string(input))
	if err != nil {
		return fmt.Sprintf("Lexer error: %v\n", err)
	}

	state := State{Data: symbols, Offset: 0}
	ast, _, err := parse(state)
	if err != nil {
		return fmt.Sprintf("Parser error: %v\n", err)
	}

	program := convert(ast)

	vars := run(program)

	result := ""
	for i, v := range vars {
		if v != 0 {
			result += fmt.Sprintf("%c = %d\n", 'a'+i, v)
		}
	}
	return result
}

func main() {
	fmt.Print(ReadAndExecute(os.Stdin))
}
