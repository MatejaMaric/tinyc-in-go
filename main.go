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
	"errors"
	"fmt"
	"io"
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

func isReservedWord(str string) (*Symbol, bool) {
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
	runeIndex := 0
	runeList := []rune(text)

	next_char := func() (rune, error) {
		if runeIndex > len(runeList)-1 {
			return 0, io.EOF
		}
		char := runeList[runeIndex]
		runeIndex++
		return char, nil
	}

	peek_char := func() (rune, error) {
		if runeIndex > len(runeList)-1 {
			return 0, io.EOF
		}
		return runeList[runeIndex], nil
	}

	symbols := []Symbol{}
	for {
		sym, err := next_symbol(next_char, peek_char)
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

func next_symbol(next_char, peek_char func() (rune, error)) (*Symbol, error) {
	c, err := next_char()
	if errors.Is(err, io.EOF) {
		return &Symbol{Type: END, Value: ""}, nil
	}
	if err != nil {
		return nil, err
	}

	handleInteger := func() (*Symbol, error) {
		val := 0
		for unicode.IsDigit(c) {
			val = val*10 + int(c-'0')

			c, err = peek_char()
			if errors.Is(err, io.EOF) {
				break
			}
			if err != nil {
				return nil, err
			}

			if unicode.IsDigit(c) {
				c, err = next_char()
				if errors.Is(err, io.EOF) {
					break
				}
				if err != nil {
					return nil, err
				}
			}
		}
		return &Symbol{Type: INTEGER, Value: strconv.Itoa(val)}, nil
	}

	handleLetters := func() (*Symbol, error) {
		runeList := []rune{}
		for unicode.IsLetter(c) {
			runeList = append(runeList, c)

			c, err = peek_char()
			if errors.Is(err, io.EOF) {
				break
			}
			if err != nil {
				return nil, err
			}

			if unicode.IsLetter(c) {
				c, err = next_char()
				if errors.Is(err, io.EOF) {
					break
				}
				if err != nil {
					return nil, err
				}
			}
		}
		if len(runeList) == 1 {
			return &Symbol{Type: VARIABLE, Value: string(runeList)}, nil
		}
		sym, ok := isReservedWord(string(runeList))
		if !ok {
			return nil, fmt.Errorf("Unknown reserved word: %s", string(runeList))
		}
		return sym, nil
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
			return handleInteger()
		} else if unicode.IsLetter(c) {
			return handleLetters()
		}
	}

	return nil, errors.New("Unknown symbol")
}

func main() {
}
