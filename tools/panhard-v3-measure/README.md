# panhard-v3-measure

Whole-set diversity score from the vendored `panhard-xz` script (xz + bc).
Higher is more diverse. Needs `xz` and `bc` on PATH for a real score.

```python
from pathlib import Path
from panhard_v3_measure import score
score(Path("tests/"))
```
