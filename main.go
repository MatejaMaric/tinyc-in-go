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

func main() {
}
