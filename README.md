# Composable Monoids in Futhark [![CI](https://github.com/diku-dk/monoidal/workflows/CI/badge.svg)](https://github.com/diku-dk/monoidal/actions) [![Documentation](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/status.svg)](https://futhark-lang.org/pkgs/github.com/diku-dk/monoidal/latest/)

A library for composable monoids in Futhark. The library allows for processing
formatted byte sequences using a single monoidal operation. Examples include
finding the maximum average of grouped floats. The library is heavily inspired by
Oleg Kiselyov's paper [More Fun with Monoids](https://okmij.org/ftp/Algorithms/monoid-fun.pdf)
and the associated OCaml code.

## Installation

```
$ futhark pkg add github.com/diku-dk/monoidal
$ futhark pkg sync
```

## Test Usage

To test the library, run the associated examples, as follows:
```
$ futhark test lib/github.com/diku-dk/monoidal/monoidal_ex.fut
```

## License

MIT License - see the associated [LICENSE](LICENSE) file.
