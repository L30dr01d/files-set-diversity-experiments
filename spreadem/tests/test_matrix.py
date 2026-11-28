import pytest
from spreadem import build_matrix


def test_limits_and_identity():
    rows = [{"id": str(i), "index": i} for i in range(256)]
    assert build_matrix([]) == {"include": []}
    assert build_matrix(rows) == {"include": rows}
    for invalid in (
        rows + [{"id": "extra"}],
        rows[:1] * 2,
        [{"id": ""}],
        [{"id": "x", "bad": {1}}],
    ):
        with pytest.raises(ValueError):
            build_matrix(invalid)
