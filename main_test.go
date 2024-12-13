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
	"encoding/json"
	"fmt"
	"io"
	"os"
	"reflect"
	"slices"
	"strings"
	"testing"
)

func TestSymbolString(t *testing.T) {
	type TestCase struct {
		symbol   Symbol
		expected string
	}

	testCases := []TestCase{
		{
			symbol:   Symbol{VARIABLE, "a"},
			expected: "VARIABLE(a)",
		},
		{
			symbol:   Symbol{EQUAL, "="},
			expected: "EQUAL(=)",
		},
		{
			symbol:   Symbol{INTEGER, "2"},
			expected: "INTEGER(2)",
		},
		{
			symbol:   Symbol{LESS, "<"},
			expected: "LESS(<)",
		},
		{
			symbol:   Symbol{SEMICOLON, ";"},
			expected: "SEMICOLON(;)",
		},
		{
			symbol:   Symbol{END, ""},
			expected: "END()",
		},
	}

	for _, tc := range testCases {
		if got := tc.symbol.String(); got != tc.expected {
			t.Errorf("\nExpected:\t%s\nGot:\t%s", tc.expected, got)
		}
	}
}

func TestLex(t *testing.T) {
	type TestCase struct {
		input    string
		expected []Symbol
	}

	testCases := []TestCase{
		{
			input: "a=b=c=2<3;",
			expected: []Symbol{
				{VARIABLE, "a"},
				{EQUAL, "="},
				{VARIABLE, "b"},
				{EQUAL, "="},
				{VARIABLE, "c"},
				{EQUAL, "="},
				{INTEGER, "2"},
				{LESS, "<"},
				{INTEGER, "3"},
				{SEMICOLON, ";"},
				{END, ""},
			},
		},
		{
			input: "{ i=1; while (i<100) i=i+i; }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "100"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{PLUS, "+"},
				{VARIABLE, "i"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
		{
			input: "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "125"},
				{SEMICOLON, ";"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{INTEGER, "100"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{MINUS, "-"},
				{VARIABLE, "j"},
				{RIGHT_PARN, ")"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{VARIABLE, "j"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{VARIABLE, "j"},
				{MINUS, "-"},
				{VARIABLE, "i"},
				{SEMICOLON, ";"},
				{ELSE_SYM, "else"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{MINUS, "-"},
				{VARIABLE, "j"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
		{
			input: "{ i=1; do i=i+10; while (i<50); }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{DO_SYM, "do"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{PLUS, "+"},
				{INTEGER, "10"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "50"},
				{RIGHT_PARN, ")"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
		{
			input: "{ i=1; while ((i=i+10)<50) ; }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{PLUS, "+"},
				{INTEGER, "10"},
				{RIGHT_PARN, ")"},
				{LESS, "<"},
				{INTEGER, "50"},
				{RIGHT_PARN, ")"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
		{
			input: "{ i=7; if (i<5) x=1; if (i<10) y=2; }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "7"},
				{SEMICOLON, ";"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "5"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "x"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "10"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "y"},
				{EQUAL, "="},
				{INTEGER, "2"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
		{
			input: "{ if (i=1) j=2; }",
			expected: []Symbol{
				{LEFT_BRACKET, "{"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{INTEGER, "2"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
		},
	}

	testFunc := func(tc TestCase) func(*testing.T) {
		return func(t *testing.T) {
			res, err := lex(tc.input)
			if err != nil {
				t.Fatalf("Unexpected error: %v", err)
			}
			if !slices.Equal(res, tc.expected) {
				t.Errorf("\nExpected:\t%v\nGot:\t\t%v", tc.expected, res)
			}
		}
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), testFunc(tc))
	}
}

func TestNodeString(t *testing.T) {
	type TestCase struct {
		node     *Node
		expected string
	}

	testCases := []TestCase{
		{
			node:     NewNodeV(VAR_NODE, 1),
			expected: fmt.Sprintf("\n(VAR_NODE(1)<nil> <nil> <nil>)"),
		},
	}

	for _, tc := range testCases {
		if got := tc.node.String(); got != tc.expected {
			t.Errorf("\nExpected:\t%s\nGot:\t%s", tc.expected, got)
		}
	}
}

type ParserTestCase struct {
	input    []Symbol
	expected *Node
}

func ParserTestFunc(logFilePrefix string, tc ParserTestCase, parser Parser) func(*testing.T) {
	return func(t *testing.T) {
		state := State{Data: tc.input, Offset: 0}
		root, state, err := parser(state)
		if err != nil {
			t.Errorf("Unexpected error: %v", err)
		}
		if sym := peek(state); sym.Type != END {
			t.Errorf("Expected END, got %s", sym)
		}
		if !reflect.DeepEqual(root, tc.expected) {
			t.Errorf("\nExpected:\t%v\nGot:\t\t%v", tc.expected, root)

			expectedTree, _ := json.MarshalIndent(tc.expected, "", "  ")
			outputTree, _ := json.MarshalIndent(root, "", "  ")

			os.WriteFile(fmt.Sprintf("./%s_expected_tree.json", logFilePrefix), expectedTree, 0644)
			os.WriteFile(fmt.Sprintf("./%s_output_tree.json", logFilePrefix), outputTree, 0644)
		}
	}
}

func TestSum(t *testing.T) {
	testCases := []ParserTestCase{
		{
			input: []Symbol{
				{VARIABLE, "b"},
				{END, ""},
			},
			expected: NewNodeV(VAR_NODE, 1),
		},
		{
			input: []Symbol{
				{VARIABLE, "b"},
				{PLUS, "+"},
				{INTEGER, "2"},
				{END, ""},
			},
			expected: NewNode2(ADD,
				NewNodeV(VAR_NODE, 1),
				NewNodeV(CONST, 2),
			),
		},
		{
			input: []Symbol{
				{VARIABLE, "b"},
				{MINUS, "-"},
				{INTEGER, "2"},
				{PLUS, "+"},
				{INTEGER, "3"},
				{END, ""},
			},
			expected: NewNode2(ADD,
				NewNode2(SUB,
					NewNodeV(VAR_NODE, 1),
					NewNodeV(CONST, 2),
				),
				NewNodeV(CONST, 3),
			),
		},
		{
			input: []Symbol{
				{VARIABLE, "b"},
				{MINUS, "-"},
				{INTEGER, "2"},
				{PLUS, "+"},
				{INTEGER, "3"},
				{MINUS, "-"},
				{INTEGER, "2"},
				{END, ""},
			},
			expected: NewNode2(SUB,
				NewNode2(ADD,
					NewNode2(SUB,
						NewNodeV(VAR_NODE, 1),
						NewNodeV(CONST, 2),
					),
					NewNodeV(CONST, 3),
				),
				NewNodeV(CONST, 2),
			),
		},
		{
			input: []Symbol{
				{LEFT_PARN, "("},
				{LEFT_PARN, "("},
				{VARIABLE, "b"},
				{RIGHT_PARN, ")"},
				{RIGHT_PARN, ")"},
				{END, ""},
			},
			expected: NewNodeV(VAR_NODE, 1),
		},
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), ParserTestFunc(fmt.Sprintf("sum_example_%d", i+1), tc, sum))
	}
}

func TestParser(t *testing.T) {
	testCases := []ParserTestCase{
		{
			input: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "125"},
				{SEMICOLON, ";"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{INTEGER, "100"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{MINUS, "-"},
				{VARIABLE, "j"},
				{RIGHT_PARN, ")"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{VARIABLE, "j"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{VARIABLE, "j"},
				{MINUS, "-"},
				{VARIABLE, "i"},
				{SEMICOLON, ";"},
				{ELSE_SYM, "else"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{MINUS, "-"},
				{VARIABLE, "j"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
			// "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }",
			expected: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode2(SEQUENCE,
							NewNode(EMPTY),
							// i=125;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 125))),
						),
						// j=100;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9), NewNodeV(CONST, 100))),
					),
					NewNode2(WHILE,
						// (i-j)
						NewNode2(SUB, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
						NewNode3(IF_ELSE,
							// (i<j)
							NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
							// j=j-i;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9),
								NewNode2(SUB, NewNodeV(VAR_NODE, 9), NewNodeV(VAR_NODE, 8)),
							)),
							// i=i-j;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8),
								NewNode2(SUB, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
							)),
						),
					),
				),
			),
		},
		{
			input: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{DO_SYM, "do"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{VARIABLE, "i"},
				{PLUS, "+"},
				{INTEGER, "10"},
				{SEMICOLON, ";"},
				{WHILE_SYM, "while"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "50"},
				{RIGHT_PARN, ")"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
			// "{ i=1; do i=i+10; while (i<50); }",
			expected: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode(EMPTY),
						// i=1;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 1))),
					),
					NewNode2(DO,
						// i=i+10;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8),
							NewNode2(ADD, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 10)),
						)),
						// (i<50)
						NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 50)),
					),
				),
			),
		},
		{
			input: []Symbol{
				{LEFT_BRACKET, "{"},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "7"},
				{SEMICOLON, ";"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "5"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "x"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{SEMICOLON, ";"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{LESS, "<"},
				{INTEGER, "10"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "y"},
				{EQUAL, "="},
				{INTEGER, "2"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
			// "{ i=7; if (i<5) x=1; if (i<10) y=2; }",
			expected: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode2(SEQUENCE,
							NewNode(EMPTY),
							// i=7;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 7))),
						),
						NewNode2(IF,
							// (i<5)
							NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 5)),
							// x=1;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, int64('x'-'a')), NewNodeV(CONST, 1))),
						),
					),
					NewNode2(IF,
						// (i<10)
						NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 10)),
						// y=2;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, int64('y'-'a')), NewNodeV(CONST, 2))),
					),
				),
			),
		},
		{
			input: []Symbol{
				{SEMICOLON, ";"},
				{END, ""},
			},
			// ";",
			expected: NewNode1(PROG, NewNode(EMPTY)),
		},
		{
			input: []Symbol{
				{LEFT_BRACKET, "{"},
				{IF_SYM, "if"},
				{LEFT_PARN, "("},
				{VARIABLE, "i"},
				{EQUAL, "="},
				{INTEGER, "1"},
				{RIGHT_PARN, ")"},
				{VARIABLE, "j"},
				{EQUAL, "="},
				{INTEGER, "2"},
				{SEMICOLON, ";"},
				{RIGHT_BRACKET, "}"},
				{END, ""},
			},
			expected: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode(EMPTY),
					NewNode2(IF,
						// (i=1)
						NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 1)),
						// j=2;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9), NewNodeV(CONST, 2))),
					),
				),
			),
		},
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), ParserTestFunc(fmt.Sprintf("parser_example_%d", i+1), tc, parse))
	}
}

func TestInstructionString(t *testing.T) {
	type TestCase struct {
		inst     Instruction
		expected string
	}
	testCases := []TestCase{
		{NewInst(IPUSH), "IPUSH"},
		{NewValueInst(1), "1"},
		{NewInst(ISTORE), "ISTORE"},
		{NewValueInst(8), "8"},
	}

	for _, tc := range testCases {
		if got := tc.inst.String(); got != tc.expected {
			t.Errorf("\nExpected:\t%s\nGot:\t%s", tc.expected, got)
		}
	}
}

func TestConvert(t *testing.T) {
	type TestCase struct {
		input    *Node
		expected []Instruction
	}

	testCases := []TestCase{
		{
			// "{ i=1; do i=i+10; while (i<50); }",
			input: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode(EMPTY),
						// i=1;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 1))),
					),
					NewNode2(DO,
						// i=i+10;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8),
							NewNode2(ADD, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 10)),
						)),
						// (i<50)
						NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 50)),
					),
				),
			),
			expected: []Instruction{
				// i=1;
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// i=i+10;
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(10),
				NewInst(IADD),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// do while (i<50);
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(50),
				NewInst(ILT),
				NewInst(JNZ),
				NewValueInst(-14),

				// end
				NewInst(HALT),
			},
		},
		{
			// "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }",
			input: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode2(SEQUENCE,
							NewNode(EMPTY),
							// i=125;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 125))),
						),
						// j=100;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9), NewNodeV(CONST, 100))),
					),
					NewNode2(WHILE,
						// (i-j)
						NewNode2(SUB, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
						NewNode3(IF_ELSE,
							// (i<j)
							NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
							// j=j-i;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9),
								NewNode2(SUB, NewNodeV(VAR_NODE, 9), NewNodeV(VAR_NODE, 8)),
							)),
							// i=i-j;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8),
								NewNode2(SUB, NewNodeV(VAR_NODE, 8), NewNodeV(VAR_NODE, 9)),
							)),
						),
					),
				),
			),
			expected: []Instruction{
				// i=125;
				NewInst(IPUSH),
				NewValueInst(125),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// j=100;
				NewInst(IPUSH),
				NewValueInst(100),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),

				// while (i-j)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ISUB),
				NewInst(JZ),
				NewValueInst(28),

				// if (i<j)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(11),

				// j=j-i;
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(ISUB),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),
				NewInst(JMP),
				NewValueInst(9),

				// i=i-j;
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ISUB),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// back to while
				NewInst(JMP),
				NewValueInst(-33),

				// end
				NewInst(HALT),
			},
		},
		{
			// "{ i=7; if (i<5) x=1; if (i<10) y=2; }",
			input: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode2(SEQUENCE,
						NewNode2(SEQUENCE,
							NewNode(EMPTY),
							// i=7;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 7))),
						),
						NewNode2(IF,
							// (i<5)
							NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 5)),
							// x=1;
							NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, int64('x'-'a')), NewNodeV(CONST, 1))),
						),
					),
					NewNode2(IF,
						// (i<10)
						NewNode2(LT, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 10)),
						// y=2;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, int64('y'-'a')), NewNodeV(CONST, 2))),
					),
				),
			),
			expected: []Instruction{
				// i=7;
				NewInst(IPUSH),
				NewValueInst(7),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// if (i<5)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(5),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(6),

				// x=1;
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(23),
				NewInst(IPOP),

				// if (i<10)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(10),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(6),

				// y=2;
				NewInst(IPUSH),
				NewValueInst(2),
				NewInst(ISTORE),
				NewValueInst(24),
				NewInst(IPOP),

				// end
				NewInst(HALT),
			},
		},
		{
			// "{ if (i=1) j=2; }",
			input: NewNode1(PROG,
				NewNode2(SEQUENCE,
					NewNode(EMPTY),
					NewNode2(IF,
						// (i=1)
						NewNode2(SET, NewNodeV(VAR_NODE, 8), NewNodeV(CONST, 1)),
						// j=2;
						NewNode1(EXPR, NewNode2(SET, NewNodeV(VAR_NODE, 9), NewNodeV(CONST, 2))),
					),
				),
			),
			expected: []Instruction{
				// if (i=1)
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(JZ),
				NewValueInst(6),

				// j=2;
				NewInst(IPUSH),
				NewValueInst(2),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),

				// end
				NewInst(HALT),
			},
		},
	}

	testFunc := func(tc TestCase) func(*testing.T) {
		return func(t *testing.T) {
			got := convert(tc.input)
			if !slices.Equal(tc.expected, got) {
				t.Errorf("\nExpected:\t%v\nGot:\t%v", tc.expected, got)
			}
		}
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), testFunc(tc))
	}
}

func TestRun(t *testing.T) {
	type TestCase struct {
		input    []Instruction
		expected [26]int64
	}

	testCases := []TestCase{
		{
			// "{ i=1; do i=i+10; while (i<50); }",
			input: []Instruction{
				// i=1;
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// i=i+10;
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(10),
				NewInst(IADD),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// do while (i<50);
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(50),
				NewInst(ILT),
				NewInst(JNZ),
				NewValueInst(-14),

				// end
				NewInst(HALT),
			},
			// i = 51
			expected: [26]int64{0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		},
		{
			// "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }",
			input: []Instruction{
				// i=125;
				NewInst(IPUSH),
				NewValueInst(125),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// j=100;
				NewInst(IPUSH),
				NewValueInst(100),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),

				// while (i-j)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ISUB),
				NewInst(JZ),
				NewValueInst(28),

				// if (i<j)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(11),

				// j=j-i;
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(ISUB),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),
				NewInst(JMP),
				NewValueInst(9),

				// i=i-j;
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IFETCH),
				NewValueInst(9),
				NewInst(ISUB),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// back to while
				NewInst(JMP),
				NewValueInst(-33),

				// end
				NewInst(HALT),
			},
			// i = 25, j = 25
			expected: [26]int64{0, 0, 0, 0, 0, 0, 0, 0, 25, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		},
		{
			// "{ i=7; if (i<5) x=1; if (i<10) y=2; }",
			input: []Instruction{
				// i=7;
				NewInst(IPUSH),
				NewValueInst(7),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(IPOP),

				// if (i<5)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(5),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(6),

				// x=1;
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(23),
				NewInst(IPOP),

				// if (i<10)
				NewInst(IFETCH),
				NewValueInst(8),
				NewInst(IPUSH),
				NewValueInst(10),
				NewInst(ILT),
				NewInst(JZ),
				NewValueInst(6),

				// y=2;
				NewInst(IPUSH),
				NewValueInst(2),
				NewInst(ISTORE),
				NewValueInst(24),
				NewInst(IPOP),

				// end
				NewInst(HALT),
			},
			// i = 7, y = 2
			expected: [26]int64{0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0},
		},
		{
			// "{ if (i=1) j=2; }",
			input: []Instruction{
				// if (i=1)
				NewInst(IPUSH),
				NewValueInst(1),
				NewInst(ISTORE),
				NewValueInst(8),
				NewInst(JZ),
				NewValueInst(6),

				// j=2;
				NewInst(IPUSH),
				NewValueInst(2),
				NewInst(ISTORE),
				NewValueInst(9),
				NewInst(IPOP),

				// end
				NewInst(HALT),
			},
			expected: [26]int64{0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		},
	}

	testFunc := func(tc TestCase) func(*testing.T) {
		return func(t *testing.T) {
			got := run(tc.input)
			if got != tc.expected {
				t.Errorf("\nExpected:\t%d\nGot:\t%d", tc.expected, got)
			}
		}
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), testFunc(tc))
	}
}

func TestReadAndExecute(t *testing.T) {
	type TestCase struct {
		input    io.Reader
		expected string
	}

	testCases := []TestCase{
		{
			input:    strings.NewReader("{ i=7; if (i<5) x=1; if (i<10) y=2; }"),
			expected: fmt.Sprintf("i = 7\ny = 2\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if (i<5) x=something; }"),
			expected: fmt.Sprintf("Lexer error: Unknown reserved word: something\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if (i<5) $x=3; }"),
			expected: fmt.Sprintf("Lexer error: Unknown symbol: $\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if (i<5) x=; }"),
			expected: fmt.Sprintf("Parser error: Expected VARIABLE, INTEGER or LEFT_PARN, got SEMICOLON(;)\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if (i<5 x=1; }"),
			expected: fmt.Sprintf("Parser error: Expected RIGHT_PARN, got VARIABLE(x)\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if i<5) x=1; }"),
			expected: fmt.Sprintf("Parser error: Expected LEFT_PARN, got VARIABLE(i)\n"),
		},
		{
			input:    strings.NewReader("{ i=7; if (i<5) x=1 }"),
			expected: fmt.Sprintf("Parser error: Expected SEMICOLON, got RIGHT_BRACKET(})\n"),
		},
		{
			input:    strings.NewReader("{ i=1; do i=i+10; (i<50); }"),
			expected: fmt.Sprintf("Parser error: Expected WHILE_SYM, got LEFT_PARN(()\n"),
		},
		{
			input:    strings.NewReader("{ i=1; do i=i+10; while (i<50) }"),
			expected: fmt.Sprintf("Parser error: Expected SEMICOLON, got RIGHT_BRACKET(})\n"),
		},
	}

	for _, tc := range testCases {
		if got := ReadAndExecute(tc.input); got != tc.expected {
			t.Errorf("\nExpected:\t%s\nGot:\t%s", tc.expected, got)
		}
	}
}
