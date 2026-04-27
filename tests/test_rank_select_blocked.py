"""Branchwise validation: blocked rank-select circuit == scan rank-select circuit.

Both ``rank_select_binary`` and ``rank_select_binary_blocked`` are
@coherent permutations on basis states. Compiling each via the b01t
QiskitBackend and running the resulting permutation circuit as a
classical bit emulator on every (occ, selector) basis state is the
b01t branchwise-validation pattern (same as ``demos/rollout/*/eval.py``).
"""
from __future__ import annotations

from math import ceil, log2

import pytest

from qiskit import QuantumCircuit

from b01t import QiskitBackend, lower_exact_program
from b01t.core import QReg
from b01t.kit.arithmetic import int_to_bits
from b01t.zoo.rank_select import (
    rank_select_binary,
    rank_select_binary_blocked,
)


def _emulate_basis_circuit(qc: QuantumCircuit, initial_bits: list[int]) -> list[int]:
    """Run a permutation circuit (X/CX/CCX/MCX) classically."""
    bits = list(initial_bits)
    qubit_index = {q: qc.find_bit(q).index for q in qc.qubits}
    for inst in qc.data:
        name = inst.operation.name
        qinds = [qubit_index[q] for q in inst.qubits]
        if name == "x":
            bits[qinds[0]] ^= 1
        elif name in {"cx", "ccx", "mcx"}:
            if all(bits[i] == 1 for i in qinds[:-1]):
                bits[qinds[-1]] ^= 1
        elif name == "barrier":
            continue
        else:
            raise ValueError(f"basis emulator saw non-classical gate {name!r}")
    return bits


def _compile(coherent_fn, n: int, w: int, idx_w: int):
    occ = QReg("occ", n)
    sel = QReg("sel", w)
    tgt = QReg("tgt", idx_w)
    prog = coherent_fn.build_exact(occ, sel, tgt)
    qc = QiskitBackend().emit(lower_exact_program(prog))
    layout: dict[str, tuple[int, int]] = {}
    offset = 0
    for r in qc.qregs:
        layout[r.name] = (offset, r.size)
        offset += r.size
    return qc, layout


def _read_target(bits: list[int], layout: dict, idx_w: int) -> int:
    tgt_start, _ = layout["tgt"]
    val = 0
    for i in range(idx_w):
        val |= bits[tgt_start + i] << i
    return val


def _run(qc: QuantumCircuit, layout: dict, occ_v: int, sel_v: int, idx_w: int) -> int:
    occ_start, occ_w = layout["occ"]
    sel_start, sel_w = layout["sel"]
    init = [0] * qc.num_qubits
    for i, b in enumerate(int_to_bits(occ_v, occ_w)):
        init[occ_start + i] = b
    for i, b in enumerate(int_to_bits(sel_v, sel_w)):
        init[sel_start + i] = b
    out = _emulate_basis_circuit(qc, init)
    return _read_target(out, layout, idx_w)


@pytest.mark.parametrize("n", [2, 3, 4, 5, 6, 7, 8])
def test_blocked_matches_scan_on_all_basis_states(n: int) -> None:
    """Compiled blocked circuit and scan circuit agree on every basis state."""
    w = max(1, ceil(log2(n + 1)))
    idx_w = w
    scan_qc, scan_layout = _compile(rank_select_binary, n, w, idx_w)
    block_qc, block_layout = _compile(rank_select_binary_blocked, n, w, idx_w)

    for occ_v in range(1 << n):
        for sel_v in range(1 << w):
            scan_out = _run(scan_qc, scan_layout, occ_v, sel_v, idx_w)
            block_out = _run(block_qc, block_layout, occ_v, sel_v, idx_w)
            assert scan_out == block_out, (
                f"mismatch n={n} occ={occ_v:0{n}b} sel={sel_v}: "
                f"scan={scan_out} blocked={block_out}"
            )


def test_blocked_returns_correct_for_dense_mask() -> None:
    """Standalone correctness: all-1 mask, rank-th bit at position rank."""
    n = 5
    w = max(1, ceil(log2(n + 1)))
    idx_w = w
    qc, layout = _compile(rank_select_binary_blocked, n, w, idx_w)

    # In the existing rank-select API, occ=1 means OCCUPIED, so an
    # all-zero occ register encodes the all-valid mask.
    occ_v = 0  # all valid
    for rank in range(n):
        out = _run(qc, layout, occ_v, rank, idx_w)
        assert out == rank, f"all-valid mask, rank={rank}: got {out}"
    # Out-of-range rank -> sentinel (= n)
    for rank in range(n, 1 << w):
        out = _run(qc, layout, occ_v, rank, idx_w)
        assert out == n, f"out-of-range rank={rank}: got {out}, expected sentinel {n}"
