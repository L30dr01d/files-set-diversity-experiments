# fast-filter

Inadequate (fixed-budget) FAST-R wrapper. Uses https://github.com/L3odr0id/FAST-R.git.

```bash
uv run python -m fast_filter path/to/dataset --algo FAST++ --percent 50
# or, after install:
fast-filter path/to/dataset --algo FAST++ --percent 50
```

Prints kept basenames to stdout, one per line.

```python
from pathlib import Path
from fast_filter import reduce
reduce(Path("tests/"), algo="FAST++", target_percent=50)
```

Algorithms: `FAST++`, `FAST-CS`, `FAST-pw`. No adequate mode.

Real FAST-R needs Python 3.14+ and `fast-filter[fastr]`; unit tests do not install it.
