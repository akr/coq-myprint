# myprint plugin for Coq

This software provides Coq commands to print Gallina terms.

## Requiements

- Coq 8.6 (Coq 8.5 doesn't work)
- OCaml 4.03 (OCaml 4.02 doesn't work)

## How to build

    make

## How to run

    coqide -I src -Q theories myprint sample/print.v

## How to use

See sample/ directory.

## Author

Tanaka Akira
