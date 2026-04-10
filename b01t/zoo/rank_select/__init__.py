"""Rank-select: coherent legal-action indexing.

Implements coherent rank-select (QCE26, Section 4.1):

    |s⟩|r⟩|0^N⟩  →  |s⟩|r⟩|e_{j_s(r)}⟩

where j_s(r) is the r-th valid cell under validity mask s.
All ancillae are fully uncomputed.
"""
from .core import rank_select, rank_select_scan, rank_select_binary, rank_select_binary_scan
