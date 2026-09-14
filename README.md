# Wire: Automated Initialization in Go

[![Build Status](https://github.com/verystar/wire/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/verystar/wire/actions)
[![godoc](https://godoc.org/github.com/verystar/wire?status.svg)][godoc]

> [!NOTE]
> This repository is a fork of [google/wire](https://github.com/google/wire),
> maintained by [verystar](https://github.com/verystar). It is intended for
> internal use by the VeryStar team only; external projects should depend on
> the upstream [google/wire](https://github.com/google/wire) or another
> community fork instead. The upstream project is no longer maintained; this
> fork continues maintenance with a focus on Go toolchain compatibility and
> bug fixes.
>
> The module path is `github.com/verystar/wire`. Existing internal projects
> can adopt this fork without changing their imports:
>
> ```shell
> go mod edit -replace=github.com/google/wire=github.com/verystar/wire@latest
> ```

Wire is a code generation tool that automates connecting components using
[dependency injection][]. Dependencies between components are represented in
Wire as function parameters, encouraging explicit initialization instead of
global variables. Because Wire operates without runtime state or reflection,
code written to be used with Wire is useful even for hand-written
initialization.

For an overview, see the [introductory blog post][].

[dependency injection]: https://en.wikipedia.org/wiki/Dependency_injection
[introductory blog post]: https://blog.golang.org/wire
[godoc]: https://godoc.org/github.com/verystar/wire

## Installing

Install Wire by running:

```shell
go install github.com/verystar/wire/cmd/wire@latest
```

and ensuring that `$GOPATH/bin` is added to your `$PATH`.

## Documentation

- [Tutorial][]
- [User Guide][]
- [Best Practices][]
- [FAQ][]

[Tutorial]: ./_tutorial/README.md
[Best Practices]: ./docs/best-practices.md
[FAQ]: ./docs/faq.md
[User Guide]: ./docs/guide.md

## Project status

This fork follows a *preserve, not extend* policy: wire's core invariant —
dependency identity is Go type identity (`types.Identical`) — is kept
unchanged, and no new feature surface is planned. Maintenance is limited to
compatibility with new Go releases and bug fixes.

Diverges from upstream `google/wire` so far:

- Module path renamed to `github.com/verystar/wire` (imports and the
  generated `//go:generate` directive point to this fork).

## Community

For questions, please use [GitHub Discussions](https://github.com/verystar/wire/discussions).

This project is covered by the Go [Code of Conduct][].

[Code of Conduct]: ./CODE_OF_CONDUCT.md
