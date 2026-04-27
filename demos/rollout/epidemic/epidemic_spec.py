"""Specification for the SIR epidemic intervention model.

Grid of N = rows * cols sites, each in state S (susceptible), I (infected),
or R (recovered).  Encoded as 2 bits per site: (inf, rem).

  S = (0, 0), I = (1, 0), R = (*, 1)
"""

import math
from dataclasses import dataclass
from typing import Tuple


@dataclass(frozen=True)
class EpidemicSpec:
    rows: int = 3
    cols: int = 3
    horizon: int = 1
    threshold: int = 2
    initial_infected: Tuple[int, ...] = (4,)  # center of 3x3
    die_sides: int = 8
    beta_num: int = 1   # beta = 1/8 (subcritical: kappa*p = 4*1/8 = 1/2 < 1)
    beta_den: int = 8
    gamma_num: int = 1  # gamma = 1/4
    gamma_den: int = 4

    @property
    def n_cells(self) -> int:
        return self.rows * self.cols

    @property
    def die_width(self) -> int:
        return max(1, math.ceil(math.log2(self.die_sides)))

    @property
    def max_degree(self) -> int:
        return min(4, 2 * (self.rows > 1) + 2 * (self.cols > 1))

    @property
    def cnt_width(self) -> int:
        return max(1, math.ceil(math.log2(self.max_degree + 1)))

    @property
    def count_width(self) -> int:
        return max(1, math.ceil(math.log2(self.n_cells + 1)))

    @property
    def n_susceptible_initially(self) -> int:
        return self.n_cells - len(self.initial_infected)

    @property
    def move_width(self) -> int:
        # Width accommodates the sentinel N for out-of-range ranks.
        return max(1, math.ceil(math.log2(self.n_cells + 1)))

    def selector_width(self, choices: int) -> int:
        if choices <= 1:
            return 0
        return math.ceil(math.log2(choices))

    def infection_threshold(self, k: int) -> int:
        t = self.die_sides * k * self.beta_num // self.beta_den
        return min(t, self.die_sides)

    def recovery_threshold(self) -> int:
        return self.die_sides * self.gamma_num // self.gamma_den

    def neighbors(self) -> list[list[int]]:
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
        n = self.n_cells
        H = self.horizon
        mw = self.move_width
        specs: list[tuple[str, int]] = []

        # Working registers (reused across rounds)
        specs.append(("inf_work", n))
        specs.append(("rem_work", n))
        specs.append(("occ_work", n))

        # Per-round output state
        for h in range(1, H + 1):
            specs.append((f"inf_{h}", n))
            specs.append((f"rem_{h}", n))

        # Per-round move register (binary index of vaccinated cell)
        for h in range(1, H + 1):
            specs.append((f"move_{h}", mw))

        # Selector registers
        for h in range(1, H + 1):
            choices = self.n_susceptible_initially if h == 1 else n
            sw = self.selector_width(choices)
            if sw > 0:
                specs.append((f"sel_{h}", sw))

        # Dice registers
        for h in range(1, H + 1):
            specs.append((f"dice_{h}", self.die_width * n))

        # Output
        specs.append(("payoff", 1))

        return specs
