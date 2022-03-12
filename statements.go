package main

import (
	"encoding/json"
	"fmt"
	"io"
	"reflect"
	"strconv"
	"strings"

	"github.com/pkg/errors"
)

// A statement is a slice of tokens representing an assignment statement.
// An assignment statement is something like:
//
//   json.city = "Leeds";
//
// Where 'json', '.', 'city', '=', '"Leeds"' and ';' are discrete tokens.
// Statements are stored as tokens to make sorting more efficient, and so
// that the same type can easily be used when gronning and ungronning.
type statement []token

// String returns the string form of a statement rather than the
// underlying slice of tokens
func (s statement) String() string {
	out := make([]string, 0, len(s)+2)
	for _, t := range s {
		out = append(out, t.format())
	}
	return strings.Join(out, "")
}

func (s statement) StringNL() string {
	out := make([]string, 0, len(s)+2)
	for _, t := range s {
		out = append(out, t.format())
	}
	out = append(out, "\n")
	return strings.Join(out, "")
}

// colorString returns the string form of a statement with ASCII color codes
func (s statement) colorString() string {
	out := make([]string, 0, len(s)+2)
	for _, t := range s {
		out = append(out, t.formatColor())
	}
	return strings.Join(out, "")
}

// a statementconv converts a statement to string
type statementconv func(s statement) string

// statementconv variant of statement.String
func statementToString(s statement) string {
	return s.String()
}

func statementToStringNL(s statement) string {
	return s.StringNL()
}

// statementconv variant of statement.colorString
func statementToColorString(s statement) string {
	return s.colorString()
}

// withBare returns a copy of a statement with a new bare
// word token appended to it
func (s statement) withBare(k string) statement {
	new := make(statement, len(s), len(s)+2)
	copy(new, s)
	return append(
		new,
		token{".", typDot},
		token{k, typBare},
	)
}

// jsonify converts an assignment statement to a JSON representation
func (s statement) jsonify() (statement, error) {
	// If m is the number of keys occurring in the left hand side
	// of s, then len(s) is in between 2*m+4 and 3*m+4. The resultant
	// statement j (carrying the JSON representation) is always 2*m+5
	// long. So len(s)+1 ≥ 2*m+5 = len(j). Therefore an initaial
	// allocation of j with capacity len(s)+1 will allow us to carry
	// through without reallocation.
	j := make(statement, 0, len(s)+1)
	if len(s) < 4 || s[0].typ != typBare || s[len(s)-3].typ != typEquals ||
		s[len(s)-1].typ != typSemi {
		return nil, errors.New("non-assignment statement")
	}

	j = append(j, token{"[", typLBrace})
	j = append(j, token{"[", typLBrace})
	for _, t := range s[1 : len(s)-3] {
		switch t.typ {
		case typNumericKey, typQuotedKey:
			j = append(j, t)
			j = append(j, token{",", typComma})
		case typBare:
			j = append(j, token{quoteString(t.text), typQuotedKey})
			j = append(j, token{",", typComma})
		}
	}
	if j[len(j)-1].typ == typComma {
		j = j[:len(j)-1]
	}
	j = append(j, token{"]", typLBrace})
	j = append(j, token{",", typComma})
	j = append(j, s[len(s)-2])
	j = append(j, token{"]", typLBrace})

	return j, nil
}

// withQuotedKey returns a copy of a statement with a new
// quoted key token appended to it
func (s statement) withQuotedKey(k string) statement {
	new := make(statement, len(s), len(s)+3)
	copy(new, s)
	return append(
		new,
		token{"[", typLBrace},
		token{quoteString(k), typQuotedKey},
		token{"]", typRBrace},
	)
}

// withNumericKey returns a copy of a statement with a new
// numeric key token appended to it
func (s statement) withNumericKey(k int) statement {
	new := make(statement, len(s), len(s)+3)
	copy(new, s)
	return append(
		new,
		token{"[", typLBrace},
		token{strconv.Itoa(k), typNumericKey},
		token{"]", typRBrace},
	)
}

// statements is a list of assignment statements.
// E.g statement: json.foo = "bar";
type statements []statement

// addWithValue takes a statement representing a path, copies it,
// adds a value token to the end of the statement and appends
// the new statement to the list of statements
func (ss *statements) addWithValue(path statement, value token) {
	s := make(statement, len(path), len(path)+3)
	copy(s, path)
	s = append(s, token{"=", typEquals}, value, token{";", typSemi})
	*ss = append(*ss, s)
}

// add appends a new complete statement to list of statements
func (ss *statements) add(s statement) {
	*ss = append(*ss, s)
}

// Len returns the number of statements for sort.Sort
func (ss statements) Len() int {
	return len(ss)
}

// Swap swaps two statements for sort.Sort
func (ss statements) Swap(i, j int) {
	ss[i], ss[j] = ss[j], ss[i]
}

// a statementmaker is a function that makes a statement
// from string
type statementmaker func(str string) (statement, error)

// statementFromString takes statement string, lexes it and returns
// the corresponding statement
func statementFromString(str string) statement {
	l := newLexer(str)
	s := l.lex()
	return s
}

// statementmaker variant of statementFromString
func statementFromStringMaker(str string) (statement, error) {
	return statementFromString(str), nil
}

// statementFromJson returns statement encoded by
// JSON specification
func statementFromJSONSpec(str string) (statement, error) {
	var a []interface{}
	var ok bool
	var v interface{}
	var s statement
	var t tokenTyp
	var nstr string
	var nbuf []byte

	err := json.Unmarshal([]byte(str), &a)
	if err != nil {
		return nil, err
	}
	if len(a) != 2 {
		goto out
	}

	v = a[1]
	a, ok = a[0].([]interface{})
	if !ok {
		goto out
	}

	// We'll append one initial token, then 3 tokens for each element of a,
	// then 3 closing tokens, that's alltogether 3*len(a)+4.
	s = make(statement, 0, 3*len(a)+4)
	s = append(s, token{"json", typBare})
	for _, e := range a {
		s = append(s, token{"[", typLBrace})
		switch e := e.(type) {
		case string:
			s = append(s, token{quoteString(e), typQuotedKey})
		case float64:
			nbuf, err = json.Marshal(e)
			if err != nil {
				return nil, errors.Wrap(err, "JSON internal error")
			}
			nstr = fmt.Sprintf("%s", nbuf)
			s = append(s, token{nstr, typNumericKey})
		default:
			ok = false
			goto out
		}
		s = append(s, token{"]", typRBrace})
	}

	s = append(s, token{"=", typEquals})

	switch v := v.(type) {
	case bool:
		if v {
			t = typTrue
		} else {
			t = typFalse
		}
	case float64:
		t = typNumber
	case string:
		t = typString
	case []interface{}:
		ok = (len(v) == 0)
		if !ok {
			goto out
		}
		t = typEmptyArray
	case map[string]interface{}:
		ok = (len(v) == 0)
		if !ok {
			goto out
		}
		t = typEmptyObject
	default:
		ok = (v == nil)
		if !ok {
			goto out
		}
		t = typNull
	}

	nbuf, err = json.Marshal(v)
	if err != nil {
		return nil, errors.Wrap(err, "JSON internal error")
	}
	nstr = fmt.Sprintf("%s", nbuf)
	s = append(s, token{nstr, t})

	s = append(s, token{";", typSemi})

out:
	if !ok {
		return nil, errors.New("invalid JSON layout")
	}
	return s, nil
}

// ungron turns statements into a proper datastructure
func (ss statements) toInterface() (interface{}, error) {

	// Get all the individually parsed statements
	var parsed []interface{}
	for _, s := range ss {
		u, err := ungronTokens(s)

		switch err.(type) {
		case nil:
			// no problem :)
		case errRecoverable:
			continue
		default:
			return nil, errors.Wrapf(err, "ungron failed for `%s`", s)
		}

		parsed = append(parsed, u)
	}

	if len(parsed) == 0 {
		return nil, fmt.Errorf("no statements were parsed")
	}

	merged := parsed[0]
	for _, p := range parsed[1:] {
		m, err := recursiveMerge(merged, p)
		if err != nil {
			return nil, errors.Wrap(err, "failed to merge statements")
		}
		merged = m
	}
	return merged, nil

}

// Less compares two statements for sort.Sort
// Implements a natural sort to keep array indexes in order
func (ss statements) Less(a, b int) bool {

	// ss[a] and ss[b] are both slices of tokens. The first
	// thing we need to do is find the first token (if any)
	// that differs, then we can use that token to decide
	// if ss[a] or ss[b] should come first in the sort.
	diffIndex := -1
	for i := range ss[a] {

		if len(ss[b]) < i+1 {
			// b must be shorter than a, so it
			// should come first
			return false
		}

		// The tokens match, so just carry on
		if ss[a][i] == ss[b][i] {
			continue
		}

		// We've found a difference
		diffIndex = i
		break
	}

	// If diffIndex is still -1 then the only difference must be
	// that ss[b] is longer than ss[a], so ss[a] should come first
	if diffIndex == -1 {
		return true
	}

	// Get the tokens that differ
	ta := ss[a][diffIndex]
	tb := ss[b][diffIndex]

	// An equals always comes first
	if ta.typ == typEquals {
		return true
	}
	if tb.typ == typEquals {
		return false
	}

	// If both tokens are numeric keys do an integer comparison
	if ta.typ == typNumericKey && tb.typ == typNumericKey {
		ia, _ := strconv.Atoi(ta.text)
		ib, _ := strconv.Atoi(tb.text)
		return ia < ib
	}

	// If neither token is a number, just do a string comparison
	if ta.typ != typNumber || tb.typ != typNumber {
		return ta.text < tb.text
	}

	// We have two numbers to compare so turn them into json.Number
	// for comparison
	na, _ := json.Number(ta.text).Float64()
	nb, _ := json.Number(tb.text).Float64()
	return na < nb

}

// Contains searches the statements for a given statement
// Mostly to make testing things easier
func (ss statements) Contains(search statement) bool {
	for _, i := range ss {
		if reflect.DeepEqual(i, search) {
			return true
		}
	}
	return false
}

const inObject = 1
const inArray = 2

type outputfunc func(w io.Writer, s statement, conv statementconv)

func lowMemWriter(w io.Writer, s statement, conv statementconv) {
	fmt.Fprintln(w, conv(s))
}

func lowMemWriteJSON(w io.Writer, s statement, conv statementconv) {
	t, err := s.jsonify()
	if err != nil {
		panic(err)
	}
	fmt.Fprintln(w, conv(t))
}

func recursiveStatementsFromJSON(r io.Reader, prefix statement, w io.Writer, opts int, conv statementconv) error {
	output := lowMemWriter

	if opts&optJSON == optJSON {
		output = lowMemWriteJSON
	}

	d := json.NewDecoder(r)

	// We don't necessarily need `UseNumber` - which gives us `json.Number` instead
	// of `float64` when parsing a JSON number - but it avoids a bunch of conversions
	// and assumptions when outputting the numbers later.
	d.UseNumber()

	objIndex := 0
	arrIndex := 0
	state := 0

	if opts&optStream == optStream {
		state = inArray
		output(w, statement{token{"json", typBare}, token{"=", typEquals}, token{"[]", typEmptyArray}, token{";", typSemi}}, conv)
	}

	return doParsing(prefix, d, state, 0, &objIndex, &arrIndex, w, opts, 0, conv, output)
}

func doParsing(prefix statement, d *json.Decoder, state int, depth int, objIndex *int, arrIndex *int, w io.Writer, opts int, processed int, conv statementconv, output outputfunc) error {
	prevKey := ""
	workingPrefix := prefix

	for {
		// Do we want to return only the first object if we're not
		// explicitly requesting stream mode?
		/*
			if depth == 0 && processed > 0 && opts&optStream == 0 {
				return nil
			}
		*/

		// Get a token, break if there's a not-EOF error.
		t, err := d.Token()
		if err != nil && err != io.EOF {
			return err
		}

		// We need to know if we've processed any tokens.
		processed++

		// If we're in an array, update the local prefix to include
		// the index number, e.g., `json.moose[23]`.
		if state == inArray {
			workingPrefix = append(prefix, token{"[", typLBrace}, token{fmt.Sprintf("%d", *arrIndex), typNumericKey}, token{"]", typRBrace})
		}

		switch x := t.(type) {
		case json.Delim:
			s := x.String()

			switch s {
			case "{":
				myObjIndex := 0
				if state == inArray {
					*arrIndex++
				}
				if state == inObject {
					*objIndex++
				}

				np := newPrefix(workingPrefix, prevKey)

				q := append(np, token{"=", typEquals}, token{"{}", typEmptyObject}, token{";", typSemi})
				output(w, q, conv)

				doParsing(np, d, inObject, depth+1, &myObjIndex, arrIndex, w, opts, processed, conv, output)
				continue

			// Ending an object bumps us up the stack one level.
			case "}":
				return nil

			case "[":
				myArrIndex := 0
				if state == inObject {
					*objIndex++
				}
				if state == inArray {
					*arrIndex++
				}
				np := newPrefix(workingPrefix, prevKey)
				q := append(np, token{"=", typEquals}, token{"[]", typEmptyArray}, token{";", typSemi})

				output(w, q, conv)

				// We keep the same prefix here
				doParsing(np, d, inArray, depth+1, objIndex, &myArrIndex, w, opts, processed, conv, output)
				continue

			// Ending an array bumps us up the stack one level.
			case "]":
				return nil
			}

		// Not a delimiter, it's a number or a string.
		default:
			if state == inArray {
				var q statement

				switch x.(type) {

				// Only 5 options here - https://pkg.go.dev/encoding/json#Token
				// Prime candidate for refactoring
				case bool:
					q = addBool(workingPrefix, x.(bool))

				case float64:
					q = addFloat64(workingPrefix, x.(float64))

				case json.Number:
					q = addNumber(workingPrefix, x.(json.Number))

				case string:
					q = addString(workingPrefix, x.(string))

				case nil:
					q = addNil(workingPrefix)

				default:
					// Should we error here?

				}
				output(w, q, conv)
				*arrIndex++
			}
			if state == inObject {
				// Because the tokenizer doesn't give us any
				// information about whether a string is a key or
				// not, we have to infer that from whether we're
				// A or B in the items we've seen at this level.
				if *objIndex%2 == 1 {
					np := newPrefix(workingPrefix, prevKey)
					var q statement
					switch x.(type) {

					// Only 5 options here - https://pkg.go.dev/encoding/json#Token
					// Prime candidate for refactoring
					case bool:
						q = addBool(np, x.(bool))

					case float64:
						q = addFloat64(np, x.(float64))

					case json.Number:
						q = addNumber(np, x.(json.Number))

					case string:
						q = addString(np, x.(string))

					case nil:
						q = addNil(np)

					default:
						// Should we error here?
					}
					output(w, q, conv)

				} else {
					prevKey = x.(string)
				}
				*objIndex++
			}
		}

		if err == io.EOF {
			return nil
		}
	}

	return fmt.Errorf("Unknown error")
}

// statementsFromJSON takes an io.Reader containing JSON
// and returns statements or an error on failure
func statementsFromJSON(r io.Reader, prefix statement) (statements, error) {
	var top interface{}
	d := json.NewDecoder(r)
	d.UseNumber()
	err := d.Decode(&top)
	if err != nil {
		return nil, err
	}
	ss := make(statements, 0, 32)
	ss.fill(prefix, top)
	return ss, nil
}

// fill takes a prefix statement and some value and recursively fills
// the statement list using that value
func (ss *statements) fill(prefix statement, v interface{}) {

	// Add a statement for the current prefix and value
	ss.addWithValue(prefix, valueTokenFromInterface(v))

	// Recurse into objects and arrays
	switch vv := v.(type) {

	case map[string]interface{}:
		// It's an object
		for k, sub := range vv {
			if validIdentifier(k) {
				ss.fill(prefix.withBare(k), sub)
			} else {
				ss.fill(prefix.withQuotedKey(k), sub)
			}
		}

	case []interface{}:
		// It's an array
		for k, sub := range vv {
			ss.fill(prefix.withNumericKey(k), sub)
		}
	}

}

// newPrefix returns a `prefix` with an appended item,
// quoted or bare accordingly.  Abstracted out to keep
// things more streamlined in the main `doParsing` loop.
func newPrefix(prefix statement, next string) statement {
	np := prefix
	if next != "" {
		if validIdentifier(next) {
			np = prefix.withBare(next)
		} else {
			np = prefix.withQuotedKey(next)
		}
	}
	return np
}

func addNil(ss statement) statement {
	return append(ss, token{"=", typEquals}, token{"null", typNull}, token{";", typSemi})
}

func addString(ss statement, s string) statement {
	return append(ss, token{"=", typEquals}, token{quoteString(s), typString}, token{";", typSemi})
}

func addBool(ss statement, b bool) statement {
	if b {
		return append(ss, token{"=", typEquals}, token{"true", typTrue}, token{";", typSemi})
	}
	return append(ss, token{"=", typEquals}, token{"false", typFalse}, token{";", typSemi})
}

func addFloat64(ss statement, x float64) statement {
	return append(ss, token{"=", typEquals}, token{fmt.Sprintf("%g", x), typNumber}, token{";", typSemi})
}

func addNumber(ss statement, x json.Number) statement {
	return append(ss, token{"=", typEquals}, token{x.String(), typNumber}, token{";", typSemi})
}
