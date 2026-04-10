"""Simon's algorithm: find hidden XOR-mask s where f(x) = f(x XOR s)."""
from .oracle import make_simon_oracle
from .algorithm import make_simon_algorithm
