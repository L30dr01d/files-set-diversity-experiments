# panhard-filter

Directory filter driven by the copied `panhard-xz` script. Drops the least important file until the next drop would make the diversity score strictly lower. An equal score continues. Needs `xz` and `bc` on PATH for a real run.

```bash
uv run python -m panhard_filter path/to/dataset
# or, after install:
panhard-filter path/to/dataset
```

Prints kept basenames to stdout, one per line. Source files are not modified.

```python
from pathlib import Path
from panhard_filter import filter
filter(Path("tests/"))
```
