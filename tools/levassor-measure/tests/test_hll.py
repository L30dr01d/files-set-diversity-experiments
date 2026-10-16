from levassor_measure.hll import HyperLogLog


def test_empty_cardinality_is_zero() -> None:
    assert HyperLogLog(p=14).cardinality() == 0.0


def test_same_hash_stays_near_one() -> None:
    sketch = HyperLogLog(p=14)
    for _ in range(1000):
        sketch.add(0x1234567890ABCDEF)
    estimate = sketch.cardinality()
    assert 0.5 < estimate < 2.0


def test_more_distinct_hashes_increase_estimate() -> None:
    small = HyperLogLog(p=14)
    large = HyperLogLog(p=14)
    mix = 0x9E3779B97F4A7C15
    for i in range(100):
        small.add((i * mix) & ((1 << 64) - 1))
    for i in range(1000):
        large.add((i * mix) & ((1 << 64) - 1))
    assert large.cardinality() > small.cardinality()
