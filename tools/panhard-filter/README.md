# panhard-filter

Ranks a folder with the vendored `panhard-xz --verbose` and drops the least important file (smallest normalised contribution; path string breaks ties). Scoring and ranking are one script run. Source files are not modified.

```bash
panhard-filter path/to/folder
panhard-filter --dont-stop path/to/folder
```

Without `--dont-stop`, removal stops when the new set's diversity is strictly lower than the previous set. That smaller set is kept. `--dont-stop` continues until 2 files remain. If diversity never falls, both modes stop at 2 files. Kept paths are printed one per line.
