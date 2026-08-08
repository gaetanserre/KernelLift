# Eq-Lift

Tactics for unifying universe levels of equality statements in Lean 4.

## Description

Eq-Lift provides two complementary tactics for working with equality statements:

- The **`lift_eq` tactic**: Lifts both sides of an equality statement to a common universe level. The tactic automatically propagates the lifting throughout operators and primitives, ensuring that the entire expression is consistently lifted. It is made to be modular and can be extended to handle new types, operators, and primitives as needed.

- The **`unlift_eq` tactic**: Reverses the lifting process. Transforms lifted equality statements back to their original universe levels, ensuring that the expressions are returned to their initial form.

For now, these tactics work with probability kernels, but can easily be extended to other types of expressions. See [`KernelLift.lean`](EqLift/Tactic/Kernel/KernelLift.lean) and [`KernelUnlift.lean`](EqLift/Tactic/Kernel/KernelUnlift.lean) for a detailed implementation of the tactics for probability kernels.

## Usage

See [`Tests.lean`](KernelLiftTests/Tests.lean) for examples of using the available tactics.

See also [Kernel-Hom](https://github.com/gaetanserre/KernelHom) for a deeper use of the kernel lifting tactic in the context of translating kernel equalities into categorical equalities.

## License

Apache 2.0. See [LICENSE](LICENSE).