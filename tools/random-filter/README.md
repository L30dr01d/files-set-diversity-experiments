# random-filter

Random-removal filtration for a set of files. The diversity metric is an argument: `metric(directory: Path) -> float`. Higher means more diverse. `new_metric.score` can be passed directly; this package does not import it.

```python
from pathlib import Path
from random import Random
from random_filter import filter_rounds, filter_subset

paths = [p for p in Path("tests").iterdir() if p.is_file()]
subset = filter_subset(paths, metric, min_keep=10, rng=Random(0))
kept = subset.kept
# subset.steps[0] is the initial score; later steps are accepted probes
result = filter_rounds(paths, metric, rounds=20, split_by=50, rng=Random(0))
```

Source files are not modified. Each probe symlinks the candidate subset into a temp directory and calls `metric` on it. A drop is kept only when `old - new <= relative_eps * old`.
