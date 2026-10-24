# random-filter

Random-removal filtration for a set of files. The diversity measure is an argument: `measure(directory: Path) -> float`. Higher means more diverse. A measure's `score` can be passed directly; this package does not import one.

```python
from pathlib import Path
from random import Random
from random_filter import filter_rounds, filter_subset

paths = [p for p in Path("tests").iterdir() if p.is_file()]
subset = filter_subset(paths, measure, rng=Random(0))
kept = subset.kept
# subset.steps[0] is the initial score; later steps are accepted probes
result = filter_rounds(paths, measure, rounds=20, split_by=50, rng=Random(0))
```

Source files are not modified. Each probe symlinks the candidate subset into a temp directory and calls `measure` on it. A drop is kept only when `old - new <= relative_eps * old`.
