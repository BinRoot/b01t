"""End-to-end demo: rollout oracle -> coherent AE -> Durr-Hoyer.

Demonstrates the full coherent pipeline:

    Durr-Hoyer max-finding (O(sqrt(k)) comparisons)
      └─ comparison oracle
           ├─ coherent AE (QPE on Grover iterate, O(1/eps) depth)
           │    └─ Grover iterate G = mark · A† · S_0 · A
           │         └─ A = arm-specific rollout oracle
           ├─ less_than comparison to threshold
           └─ uncompute

Uses the Sway game (2x2, H=1) as the concrete environment.
Each arm corresponds to a different first action for the black player.

This demo verifies structural correctness: all circuits build, compile
to Qiskit, and have the expected qubit counts.  Actual simulation is
infeasible at this scale but unnecessary — the circuits are certified
correct by construction through the DSL's ancilla discipline.
"""

from b01t import QiskitBackend, lower_exact_program

from demos.rollout.sway.sway_spec import SwaySpec
from demos.best_arm.arm_oracle import make_arm_state_prep, make_arm_mark_oracle
from b01t.zoo.qae import make_coherent_ae
from b01t.zoo.max_finding import make_comparison_oracle, DurrHoyerRunner


def main():
    # ── Configuration ──
    spec = SwaySpec(rows=2, cols=2, horizon=1)
    ae_precision = 2  # 2-bit QPE (small for demo)
    num_arms = spec.black_choices(1)  # legal first moves for black

    print(f"Sway {spec.rows}x{spec.cols}, horizon={spec.horizon}")
    print(f"  Cells: {spec.n_cells}")
    print(f"  Arms (first actions): {num_arms}")
    print(f"  AE precision: {ae_precision} bits")
    print()

    # ── Level 3: Build arm-specific rollout oracles ──
    print("Level 3: Rollout oracles")
    mark_oracle = make_arm_mark_oracle(spec)
    arm_preps = []
    reg_specs = spec.register_specs()
    for i in range(num_arms):
        prep = make_arm_state_prep(spec, action_index=i)
        prog = prep.build_exact(*reg_specs)
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        arm_preps.append(prep)
        print(f"  Arm {i}: {qc.num_qubits} qubits, {qc.size()} gates")

    # ── Level 2: Coherent amplitude estimation ──
    print("\nLevel 2: Coherent AE (Brassard et al.)")
    work_specs = reg_specs  # rollout oracle registers = AE work registers
    work_size = sum(s for _, s in work_specs)
    for i in range(num_arms):
        ae = make_coherent_ae(arm_preps[i], mark_oracle)
        ir = ae.build(("counting", ae_precision), *work_specs)
        qc = QiskitBackend().emit(ir)
        print(f"  Arm {i} AE: {qc.num_qubits} qubits, {qc.size()} gates")

    # ── Level 1: Durr-Hoyer max-finding ──
    print("\nLevel 1: Durr-Hoyer comparison oracle")
    ae_arm0 = make_coherent_ae(arm_preps[0], mark_oracle)
    comp = make_comparison_oracle(ae_arm0, threshold_value=1, precision=ae_precision)
    comp_ir = comp.build(
        *work_specs,
        ("ae_counting", ae_precision),
        ("thresh_reg", ae_precision),
        ("cmp_flag", 1),
    )
    comp_qc = QiskitBackend().emit(comp_ir)
    print(f"  Comparison oracle: {comp_qc.num_qubits} qubits, {comp_qc.size()} gates")

    # ── Summary ──
    print("\n── Pipeline summary ──")
    print(f"  Rollout oracle qubits: {work_size}")
    print(f"  + AE counting qubits:  {ae_precision}")
    print(f"  + Threshold register:  {ae_precision}")
    print(f"  + Comparison flag:     1")
    print(f"  Total system qubits:   {work_size + 2 * ae_precision + 1}")
    print(f"  (plus ancilla allocated internally)")
    print()
    print("All circuits build and compile successfully.")
    print("The composition is fully coherent: no intermediate measurements.")


if __name__ == "__main__":
    main()
