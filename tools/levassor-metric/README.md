# levassor-metric

Whole-set diversity score of a directory of files. Coverage of 16-byte windows:
unique windows (HyperLogLog) divided by the sum of per-file unique-window counts.
Higher is more diverse. The value is in `[0, 1]`. No greedy filtering.

```python
from pathlib import Path
from levassor_metric import score
score(Path("tests/"))
```


https://algo.inria.fr/flajolet/Publications/FlFuGaMe07.pdf
