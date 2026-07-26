# Rollout Oracle - Lean 4 Proofs

Machine-checked proofs for the rank-select primitive, rollout oracle
cost formulas, classical lower bound, lifting and per-configuration
transfer theorems, and quantum upper bound used by the rollout-oracle
construction. Sits next to the Python implementation at `../sway/`,
`../epidemic/`, with the bench driver at `../bench.py`.

## Build

```bash
lake exe cache get   # download mathlib build cache (~few GB; one-time)
lake build           # compile all modules
```

Toolchain: `lean4 v4.28.0`, `mathlib4 v4.28.0`. Pinned in
`lean-toolchain` and `lakefile.toml`.

## Result-to-module map

Module names are bare Lean modules under `RolloutProofs/`. Numbering
follows the QCE 2026 paper (*Coherent Rollout Oracles for
Finite-Horizon Sequential Decision Problems*), Appendix A; the map
below mirrors that appendix.

| Paper result                                                   | Lean module                                        |
| -------------------------------------------------------------- | -------------------------------------------------- |
| Prop. 1: unconditional Omega(N) gate lower bound              | `RankSelectCommunication`                          |
| Lem. 2: rank-select cut lower bound                           | `RankSelectCommunication`                          |
| Lem. 3: crossing-gate lower bound                             | `RankSelectCommunication`, `RankSelectCircuit`     |
| Cor. 4: scan tracks prefix rank at every cut                  | `RankSelectCommunication`, `RankSelectUniversality` |
| Thm. 5: sequential-scan upper bound, O(Nw)                    | `RankSelectUpperBound`                             |
| Thm. 6: bounded-span optimality, Theta(Nw)                    | `RankSelectUpperBound`, `RankSelectGateLowerBound`, `RankSelectCommunication` |
| Thm. 7: blocked construction, O(N log w)                      | `RankSelectBlocked`                                |
| Thm. 8: polynomial-size coherent rollout oracle               | `OracleCostProof`                                  |
| Prop. 9: classical Omega(k/eps^2) lower bound                 | `RolloutLowerBound`                                |
| Thm. 10: bounded-influence lifting                            | `GeneralizedLifting`                               |
| Thm. 11: per-configuration lower-bound transfer               | `TemplateBridge` (modular, beta = 0), `ApproximateBridge` (0 < beta < eps) |
| Cor. 12: quantum O~(sqrt(k)/eps) upper bound (external axioms) | `QuantumUpperBound`                                |
| Thm. 13: subcritical influence decay (App. B)                 | `SpatialDecay`                                     |

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
    ├── RankSelectBlocked.lean
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
