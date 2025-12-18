package main

import "fmt"

type Message string
type Message2 = Message

type Pair struct{ A, B Message }

func NewMessage(s string) Message { return Message("M:" + s) }

func NewPair(a Message, b Message2) Pair { return Pair{A: a, B: b} }

func main() { fmt.Println(inject("x").A) }
