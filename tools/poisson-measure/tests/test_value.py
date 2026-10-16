from poisson_measure import poisson_measure_value


def test_poisson_measure_value_is_order_independent():
    distances_asc = {
        (0, 1): 10.0,
        (0, 2): 100.0,
        (1, 2): 1000.0,
    }
    distances_desc = {
        (1, 2): 1000.0,
        (0, 2): 100.0,
        (0, 1): 10.0,
    }
    val_asc = poisson_measure_value(distances_asc)
    val_desc = poisson_measure_value(distances_desc)
    assert abs(val_asc - val_desc) < 1e-6
