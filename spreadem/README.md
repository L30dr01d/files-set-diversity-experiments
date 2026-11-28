# SpreadEm

Install from this directory with `pip install ./spreadem` from the parent repository. The package has no runtime dependencies.

Pass one row per planned job. Each row needs a unique string ID and can carry JSON-compatible metadata for the worker.

```python
import json
from spreadem import build_matrix

print(json.dumps(build_matrix([{"id": "batch-1", "cluster_index": 0}])))
```

Use the resulting JSON as a GitHub Actions matrix through `fromJSON`. An empty plan yields an empty include list. More than 256 jobs raises `ValueError` before scheduling.
