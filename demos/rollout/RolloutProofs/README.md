# Rollout Oracle - Lean 4 Proofs

Machine-checked proofs for the rank-select primitive, rollout oracle
cost formulas, classical lower bound, lifting theorem, and quantum
upper bound used by the rollout-oracle construction. Sits next to the
Python implementation at `../sway/`, `../epidemic/`, with the bench
driver at `../bench.py`.

## Build

```bash
lake exe cache get   # download mathlib build cache (~few GB; one-time)
lake build           # compile all modules
```

Toolchain: `lean4 v4.28.0`, `mathlib4 v4.28.0`. Pinned in
`lean-toolchain` and `lakefile.toml`.

## Result-to-module map

Module names are bare Lean modules under `RolloutProofs/`.

| Result                                                 | Lean module                                        |
| ------------------------------------------------------ | -------------------------------------------------- |
| Rank-select unconditional gate lower bound             | `RankSelectCircuit`                                |
| Rank-select per-cut communication lower bound          | `RankSelectCommunication`                          |
| Rank-select crossing-bit lower bound                   | `RankSelectCommunication`                          |
| Rank-select sequential-scan upper bound (O(Nw))        | `RankSelectUpperBound`                             |
| Rank-select tightness corollary                        | `RankSelectUpperBound`, `RankSelectGateLowerBound` |
| Rank-select universality (compute-select-uncompute)    | `RankSelectUniversality`                           |
| Rollout oracle cost formula                            | `OracleCostProof`                                  |
| Classical Omega(k/eps^2) rollout lower bound           | `RolloutLowerBound`                                |
| Bounded-influence lifting theorem                      | `GeneralizedLifting`                               |
| Spatial-decay sufficient condition                     | `SpatialDecay`                                     |
| Quantum O~(sqrt(k)/eps) upper bound (external axioms)  | `QuantumUpperBound`                                |

`QuantumUpperBound` is modulo three external axioms:
`iqae_query_complexity` (Grinko et al.),
`quantum_max_finding` (Dürr–Høyer), and the `BanditAlgorithm`
interface declared in `BanditCore.lean`.

## Layout

```
RolloutProofs/
├── lakefile.toml            project + mathlib dependency
├── lake-manifest.json       resolved deps
├── lean-toolchain           pinned toolchain
├── RolloutProofs.lean       top-level entry point
└── RolloutProofs/
    ├── RankSelectCircuit.lean
    ├── RankSelectCommunication.lean
    ├── RankSelectGateLowerBound.lean
    ├── RankSelectUniversality.lean
    ├── RankSelectUpperBound.lean
    ├── OracleCostProof.lean
    ├── RolloutLowerBound.lean
    ├── GeneralizedLifting.lean
    ├── SpatialDecay.lean
    ├── QuantumUpperBound.lean
    ├── BanditCore.lean
    ├── SwayDynamics.lean
    ├── MoveValues.lean
    ├── ManyHardBoards.lean
    ├── AverageCaseHardness.lean
    ├── ApproximateBridge.lean
    ├── TemplateBridge.lean
    └── Main.lean
```
