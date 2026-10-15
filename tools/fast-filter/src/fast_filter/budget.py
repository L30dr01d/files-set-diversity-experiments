def budget_from_percent(suite_size: int, target_percent: float) -> int:
    if suite_size < 1:
        raise ValueError("suite size must be at least 1")
    if not (0 < target_percent <= 100):
        raise ValueError(
            f"target percent must be in (0, 100], got {target_percent}"
        )
    budget = int(suite_size * target_percent / 100)
    if budget < 1:
        raise ValueError(
            f"target percent {target_percent} yields budget 0 "
            f"for suite size {suite_size}"
        )
    return budget
