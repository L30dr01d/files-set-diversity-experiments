# poisson-measure

Diversity score for a directory of files: pairwise NCD distances, then a Poisson-weighted sum.

This measure was invented by contributors of the [DepTyCheck](https://github.com/DepTyCheck) GitHub organization.

```python
from pathlib import Path
from poisson_measure import score
score(Path("tests/"))
```
