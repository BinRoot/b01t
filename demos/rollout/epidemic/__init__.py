"""Epidemic (SIR) rollout oracle: coherent vaccination + infection + recovery."""
from .epidemic_spec import EpidemicSpec
from .sir_transition import make_sir_transition
from .terminal_eval import make_epidemic_terminal_eval
from .rollout_oracle import make_epidemic_rollout_oracle
