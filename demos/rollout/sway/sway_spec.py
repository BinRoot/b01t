"""Classical Sway grid/horizon spec and derived register sizes for the rollout oracle."""

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class SwaySpec:
    rows: int = 2
    cols: int = 2
    horizon: int = 1

    @property
    def n_cells(self) -> int:
        return self.rows * self.cols

    @property
    def max_degree(self) -> int:
        """Max number of orthogonal neighbors any cell can have."""
        return min(4, 2 * (self.rows > 1) + 2 * (self.cols > 1))

    @property
    def count_width(self) -> int:
        """Bits needed to count up to n_cells."""
        return max(1, math.ceil(math.log2(self.n_cells + 1)))

    @property
    def cnt_width(self) -> int:
        """Bits for neighbor count (0..max_degree)."""
        return max(1, math.ceil(math.log2(self.max_degree + 1)))

    @property
    def die_width(self) -> int:
        """Bits per die roll (0..19 for Sway)."""
        return 5

    def selector_width(self, choices: int) -> int:
        if choices <= 1:
            return 0
        return math.ceil(math.log2(choices))

    def black_choices(self, round_idx: int) -> int:
        """Empty cells available for black in round round_idx (1-based)."""
        return self.n_cells - 2 * (round_idx - 1)

    def white_choices(self, round_idx: int) -> int:
        """Empty cells available for white after black places."""
        return self.black_choices(round_idx) - 1

    def neighbors(self) -> list[list[int]]:
        """4-connected neighbor list for each cell."""
        nbrs = []
        for idx in range(self.n_cells):
            r, c = divmod(idx, self.cols)
            cell_nbrs = []
            if r > 0:
                cell_nbrs.append((r - 1) * self.cols + c)
            if r < self.rows - 1:
                cell_nbrs.append((r + 1) * self.cols + c)
            if c > 0:
                cell_nbrs.append(r * self.cols + c - 1)
            if c < self.cols - 1:
                cell_nbrs.append(r * self.cols + c + 1)
            nbrs.append(cell_nbrs)
        return nbrs

    def register_specs(self) -> list[tuple[str, int]]:
        """Return (name, size) pairs for all registers in the rollout oracle."""
        n = self.n_cells
        h = self.horizon
        specs: list[tuple[str, int]] = []

        # State registers
        specs.append(("occ", n))
        for i in range(h + 1):
            specs.append((f"color_{i}", n))

        # Move registers (binary-encoded cell index, one per placement)
        move_w = max(1, math.ceil(math.log2(n))) if n > 1 else 1
        for r in range(1, h + 1):
            specs.append((f"move_b{r}", move_w))
            specs.append((f"move_w{r}", move_w))

        # Selector registers (in superposition)
        for r in range(1, h + 1):
            specs.append((f"sel_b{r}", self.selector_width(self.black_choices(r))))
            specs.append((f"sel_w{r}", self.selector_width(self.white_choices(r))))

        # Dice registers (one per round)
        for r in range(1, h + 1):
            specs.append((f"dice_{r}", self.die_width * n))

        # Output
        specs.append(("payoff", 1))

        return specs

    @property
    def total_qubits_estimate(self) -> int:
        """Total declared qubits for the rollout oracle."""
        return sum(size for _, size in self.register_specs())
