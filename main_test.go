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
				{Type: VARIABLE, Value: "a"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "b"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "c"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "2"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "3"},
				{Type: SEMICOLON, Value: ";"},
				{Type: END, Value: ""},
			},
		},
		{
			input: "{ i=1; while (i<100) i=i+i; }",
			expected: []Symbol{
				{Type: LEFT_BRACKET, Value: "{"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "1"},
				{Type: SEMICOLON, Value: ";"},
				{Type: WHILE_SYM, Value: "while"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "100"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "i"},
				{Type: PLUS, Value: "+"},
				{Type: VARIABLE, Value: "i"},
				{Type: SEMICOLON, Value: ";"},
				{Type: RIGHT_BRACKET, Value: "}"},
				{Type: END, Value: ""},
			},
		},
		{
			input: "{ i=125; j=100; while (i-j) if (i<j) j=j-i; else i=i-j; }",
			expected: []Symbol{
				{Type: LEFT_BRACKET, Value: "{"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "125"},
				{Type: SEMICOLON, Value: ";"},
				{Type: VARIABLE, Value: "j"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "100"},
				{Type: SEMICOLON, Value: ";"},
				{Type: WHILE_SYM, Value: "while"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: MINUS, Value: "-"},
				{Type: VARIABLE, Value: "j"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: IF_SYM, Value: "if"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: LESS, Value: "<"},
				{Type: VARIABLE, Value: "j"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: VARIABLE, Value: "j"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "j"},
				{Type: MINUS, Value: "-"},
				{Type: VARIABLE, Value: "i"},
				{Type: SEMICOLON, Value: ";"},
				{Type: ELSE_SYM, Value: "else"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "i"},
				{Type: MINUS, Value: "-"},
				{Type: VARIABLE, Value: "j"},
				{Type: SEMICOLON, Value: ";"},
				{Type: RIGHT_BRACKET, Value: "}"},
				{Type: END, Value: ""},
			},
		},
		{
			input: "{ i=1; do i=i+10; while (i<50); }",
			expected: []Symbol{
				{Type: LEFT_BRACKET, Value: "{"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "1"},
				{Type: SEMICOLON, Value: ";"},
				{Type: DO_SYM, Value: "do"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "i"},
				{Type: PLUS, Value: "+"},
				{Type: INTEGER, Value: "10"},
				{Type: SEMICOLON, Value: ";"},
				{Type: WHILE_SYM, Value: "while"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "50"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: SEMICOLON, Value: ";"},
				{Type: RIGHT_BRACKET, Value: "}"},
				{Type: END, Value: ""},
			},
		},
		{
			input: "{ i=1; while ((i=i+10)<50) ; }",
			expected: []Symbol{
				{Type: LEFT_BRACKET, Value: "{"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "1"},
				{Type: SEMICOLON, Value: ";"},
				{Type: WHILE_SYM, Value: "while"},
				{Type: LEFT_PARN, Value: "("},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: VARIABLE, Value: "i"},
				{Type: PLUS, Value: "+"},
				{Type: INTEGER, Value: "10"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "50"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: SEMICOLON, Value: ";"},
				{Type: RIGHT_BRACKET, Value: "}"},
				{Type: END, Value: ""},
			},
		},
		{
			input: "{ i=7; if (i<5) x=1; if (i<10) y=2; }",
			expected: []Symbol{
				{Type: LEFT_BRACKET, Value: "{"},
				{Type: VARIABLE, Value: "i"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "7"},
				{Type: SEMICOLON, Value: ";"},
				{Type: IF_SYM, Value: "if"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "5"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: VARIABLE, Value: "x"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "1"},
				{Type: SEMICOLON, Value: ";"},
				{Type: IF_SYM, Value: "if"},
				{Type: LEFT_PARN, Value: "("},
				{Type: VARIABLE, Value: "i"},
				{Type: LESS, Value: "<"},
				{Type: INTEGER, Value: "10"},
				{Type: RIGHT_PARN, Value: ")"},
				{Type: VARIABLE, Value: "y"},
				{Type: EQUAL, Value: "="},
				{Type: INTEGER, Value: "2"},
				{Type: SEMICOLON, Value: ";"},
				{Type: RIGHT_BRACKET, Value: "}"},
				{Type: END, Value: ""},
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
