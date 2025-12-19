//go:build wireinject
// +build wireinject

package main

import "github.com/verystar/wire"

func inject(s string) Pair {
	panic(wire.Build(NewMessage, NewMessage2, NewPair))
}
