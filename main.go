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
/* Parser Combinators                                                        */
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

type Node struct {
	Type       NodeType
	Value      int64
	O1, O2, O3 *Node
}

func (n *Node) String() string {
	return fmt.Sprintf("\n(%s(%d)%s %s %s)", n.Type, n.Value, n.O1, n.O2, n.O3)
}

func NewNode(ntype NodeType) *Node {
	return &Node{ntype, 0, nil, nil, nil}
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
	Data   string
	Offset int
}

func peek(s State) rune {
	r, _ := utf8.DecodeRuneInString(s.Data[s.Offset:])
	return r
}

func consume(s State) (rune, State) {
	r, n := utf8.DecodeRuneInString(s.Data[s.Offset:])
	if r != utf8.RuneError {
		s.Offset += n
	}
	return r, s
}

type Parser func(State) (*Node, State, error)

func parse(state State) (*Node, State, error) {
	return nil, state, nil
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

	state := State{Data: string(input), Offset: 0}

	ast, state, err := parse(state)
	if err != nil {
		return fmt.Sprintf("Error while parsing: %v\n", err)
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
