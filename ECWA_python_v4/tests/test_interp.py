#!/usr/bin/env python
# Author: Timothy J. Welch
"""Tests for common.interp1 (MATLAB interp1 semantics)."""
import numpy as np
import pytest

from common.interp import interp1


def test_1d_linear_interior():
    xi = np.array([0, 1, 2, 3], float)
    yi = np.array([0, 10, 20, 30], float)
    out = interp1(xi, yi, np.array([0.5, 1.5, 2.5]))
    assert np.allclose(out, [5, 15, 25])


def test_1d_matches_numpy_interp():
    # MATLAB interp1 (NaN outside) == np.interp only on the interior; compare there.
    rng = np.random.default_rng(1)
    xi = np.sort(rng.random(50) * 10)
    yi = rng.random(50)
    xq = xi[0] + (xi[-1] - xi[0]) * rng.uniform(0.01, 0.99, 200)
    assert np.allclose(interp1(xi, yi, xq), np.interp(xq, xi, yi))


def test_boundary():
    xi = np.array([0, 1, 2, 3], float)
    yi = np.array([0, 10, 20, 30], float)
    assert np.allclose(interp1(xi, yi, np.array([0, 3])), [0, 30])


def test_outside_no_extrap_nan():
    xi = np.array([0, 1, 2, 3], float)
    yi = np.array([0, 10, 20, 30], float)
    out = interp1(xi, yi, np.array([-1, 4]))
    assert np.all(np.isnan(out))


def test_outside_extrap():
    xi = np.array([0, 1, 2, 3], float)
    yi = np.array([0, 10, 20, 30], float)
    out = interp1(xi, yi, np.array([-1, 4]), extrap=True)
    assert np.allclose(out, [-10, 40])


def test_multi_series_columns():
    xi = np.array([0, 1, 2], float)
    yi = np.array([[0, 100], [10, 110], [20, 120]], float)
    out = interp1(xi, yi, np.array([0.5, 1.5]))
    assert out.shape == (2, 2)
    assert np.allclose(out[0], [5, 105])
    assert np.allclose(out[1], [15, 115])


def test_nonuniform_xi():
    xi = np.array([0, 1, 3], float)
    yi = np.array([0, 10, 30], float)
    assert np.allclose(interp1(xi, yi, np.array([2.0])), [20.0])
