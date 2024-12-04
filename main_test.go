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
	"os"
	"reflect"
	"slices"
	"testing"
)

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
				{SEMICOLON, ";"},
				{END, ""},
			},
			// ";",
			expected: NewNode1(PROG, NewNode(EMPTY)),
		},
	}

	for i, tc := range testCases {
		t.Run(fmt.Sprintf("Example %d", i+1), ParserTestFunc(fmt.Sprintf("parser_example_%d", i+1), tc, parse))
	}
}
