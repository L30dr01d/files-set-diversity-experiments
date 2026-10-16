import numpy as np
from scipy.stats import poisson


def poisson_measure_value(distances: dict[tuple[int, int], float]) -> float:
    distance_values = np.array(list(distances.values()), dtype=np.float32)
    distance_values = np.sort(distance_values)
    dist_len = distance_values.size
    indices = np.arange(dist_len)
    weights = poisson.pmf(indices, dist_len)
    values = 2 * distance_values * weights
    return float(values.sum())
