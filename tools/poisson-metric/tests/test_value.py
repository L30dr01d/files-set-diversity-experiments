from poisson_metric import poisson_metric_value


def test_poisson_metric_value_is_order_independent():
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
    val_asc = poisson_metric_value(distances_asc)
    val_desc = poisson_metric_value(distances_desc)
    assert abs(val_asc - val_desc) < 1e-6
