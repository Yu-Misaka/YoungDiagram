# YoungDiagram

> [!TIP]
> Documentation: https://samuele0271194.github.io/YoungDiagram/docs/

[![Build project and documentation](https://github.com/SamuelE0271194/YoungDiagram/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/SamuelE0271194/YoungDiagram/actions/workflows/lean_action_ci.yml)

This Lean 4 project aims to formalize parts of Dragomir Djokovic's paper *Closures of Conjugacy Classes in Classical Real Linear Lie Groups. II* (1982).

## Current state

The project is still at an early stage, but the basic combinatorial infrastructure is already present:

- `YoungDiagram/Gene.lean` defines genes and their signatures.
- `YoungDiagram/Chromosome.lean` defines chromosomes, rank, signature, and the prime operation.
- `YoungDiagram/Variety.lean` develops varieties and lift/filter constructions.
- `YoungDiagram/Mutations*.lean` formalizes several primitive mutation patterns.
- `YoungDiagram/Sigma*.lean` contains work toward the sigma conditions and orbit-order arguments.

In terms of the paper, the present code is mainly setting up the framework around the chromosome partial order and the mutation-based approach to orbit closure.

## Building

```bash
lake build
```

For a few small experiments, see `YoungDiagram/Examples.lean`.
