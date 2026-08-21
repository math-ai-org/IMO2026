# IMO 2026 Lean Formalizations

Lean 4 formalizations of problems from the 2026 International Mathematical Olympiad.

## Status

| Problem | File | Status |
| --- | --- | --- |
| 1 | [`IMO2026P1.lean`](./IMO2026P1.lean) | Proved |
| 2 | [`IMO2026P2.lean`](./IMO2026P2.lean) | Proved |
| 3 | — | Not yet formalized |
| 4 | [`IMO2026P4.lean`](./IMO2026P4.lean) | Proved |
| 5 | [`IMO2026P5.lean`](./IMO2026P5.lean) | Proved |
| 6 | [`IMO2026P6.lean`](./IMO2026P6.lean) | Proved |

## Toolchain

- Lean `4.30.0-rc2`
- Mathlib `v4.30.0-rc2`
- Lake dependency versions are pinned in [`lake-manifest.json`](./lake-manifest.json).

## Build

Install [Lean through Elan](https://lean-lang.org/lean4/doc/setup.html), then run:

```bash
git clone https://github.com/math-ai-org/IMO2026.git
cd IMO2026
lake build
```

To build one problem only:

```bash
lake build IMO2026P5
```

Replace `IMO2026P5` with any available target listed above.

## Repository conventions

- Problem files are named `IMO2026P<N>.lean`.
- Public declarations use the namespace `IMO2026P<N>`.
- Each problem is registered as a `lean_lib` target in [`lakefile.toml`](./lakefile.toml).
- New proofs should compile with the pinned project toolchain and avoid placeholders or custom axioms.

## License

This repository is licensed under the [Apache License 2.0](./LICENSE).
