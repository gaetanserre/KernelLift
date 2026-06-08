# Kernel-Lift

Tactics for unifying universe levels when working with probability kernels in Lean.

## Description

Kernel-Lift provides two complementary tactics for working with probability kernels:

- **`kernel_lift` tactic**: Lifts kernels to a common universe level. When working with kernels of different universe levels, this tactic automatically transforms them to operate at a unified level.

- **`kernel_unlift` tactic**: Reverses the lifting process. Transforms lifted kernels back to their original universe levels.

These tactics handle several kernel operations and primitives: composition, parallel composition, product, identity, discard, copy, and swap.

## Usage

See [`Tests.lean`](KernelLiftTests/Tests.lean) for examples of using the available tactics.
