#!/usr/bin/env python
# Author: Timothy J. Welch
"""RED tests for the low-level CWA helper functions (ported from CWA_MATLAB).

These are pure-numeric helpers with hand-derived expected values, so they give
fast, independent feedback before the larger CWA / ECWA stages are validated
against the saved MATLAB ground-truth artifacts.
"""
import numpy as np
import pytest

from cwa.helpers import arg, quadfit, intersect2, fftwrap, fft2wrap


# ---------------------------------------------------------------------------
# arg(z): polar angle in [0, 2*pi)  (port of CWA_MATLAB/arg.m)
# ---------------------------------------------------------------------------
def test_arg_quadrants():
    assert np.isclose(arg(1 + 1j), np.pi / 4)
    assert np.isclose(arg(1 - 1j), 7 * np.pi / 4)
    assert np.isclose(arg(-1 + 1j), 3 * np.pi / 4)
    assert np.isclose(arg(-1 - 1j), 5 * np.pi / 4)


def test_arg_vector_and_positive_real():
    z = np.array([1 + 1j, -1 - 1j, 2 + 0j])
    out = arg(z)
    assert np.isclose(out[0], np.pi / 4)
    assert np.isclose(out[1], 5 * np.pi / 4)
    assert np.isclose(out[2], 0.0)


# ---------------------------------------------------------------------------
# quadfit(x, y): [a;b;c] normal-equation quadratic fit  (nested in CWA.m)
# ---------------------------------------------------------------------------
def test_quadfit_recovers_exact_quadratic():
    x = np.array([1.0, 2.0, 3.0, 4.0])
    y = 2 * x**2 + 3 * x + 1  # [6,15,28,45]
    p = quadfit(x, y)
    assert np.allclose(p, [2.0, 3.0, 1.0], atol=1e-9)


# ---------------------------------------------------------------------------
# intersect2(l1, l2): point-slope / unit-vector line intersection
# ---------------------------------------------------------------------------
def test_intersect2_known_lines():
    r = 1 / np.sqrt(2)
    l1 = np.array([0.0, 0.0, r, r])   # line y = x through origin
    l2 = np.array([2.0, 0.0, 0.0, 1.0])  # vertical line x = 2
    x, y = intersect2(l1, l2)
    assert np.isclose(x, 2.0)
    assert np.isclose(y, 2.0)


# ---------------------------------------------------------------------------
# fftwrap(Hz, x): one-sided amplitude spectrum
# ---------------------------------------------------------------------------
def test_fftwrap_sine_amplitude_even():
    Hz = 100.0
    N = 100
    n = np.arange(N)
    x = np.sin(2 * np.pi * 5 * n / Hz)
    f, P, phi = fftwrap(Hz, x)
    assert f.shape == (N // 2 + 1,)
    assert np.allclose(f, Hz * np.arange(N // 2 + 1) / N)
    ipeak = int(np.argmax(P))
    assert np.isclose(f[ipeak], 5.0)
    assert np.isclose(P[ipeak], 1.0, atol=1e-9)  # one-sided amplitude of a unit sine


def test_fftwrap_matrix_columns():
    Hz = 100.0
    N = 100
    n = np.arange(N)
    X = np.stack([np.sin(2 * np.pi * 5 * n / Hz),
                  0.5 * np.sin(2 * np.pi * 5 * n / Hz)], axis=1)
    f, P = fftwrap(Hz, X, nargout=2)
    assert P.shape == (N // 2 + 1, 2)
    assert np.isclose(P[5, 0], 1.0, atol=1e-9)
    assert np.isclose(P[5, 1], 0.5, atol=1e-9)


def test_fftwrap_one_output_is_f():
    # nargout == 1 in MATLAB -> return only f (length (L/2+1) after even-trim)
    out = fftwrap(100.0, np.sin(np.arange(101)), nargout=1)
    assert out.shape == (51,)  # 101 -> trimmed to 100 -> 51 bins


# ---------------------------------------------------------------------------
# fft2wrap(x, Hzx, Hzy): shifted 2D FFT + frequency axes
# ---------------------------------------------------------------------------
def test_fft2wrap_dc_peak_odd():
    Ny, Nx = 11, 13
    x = np.ones((Ny, Nx))
    P, fx, fy = fft2wrap(x, Nx, Ny)
    assert P.shape == (Ny, Nx)
    assert fx.shape == (Nx,) and fy.shape == (Ny,)
    assert np.isclose(fx[Nx // 2], 0.0) and np.isclose(fy[Ny // 2], 0.0)
    # DC energy peaks at the fftshift center
    iy, ix = np.unravel_index(np.argmax(np.abs(P)), P.shape)
    assert (iy, ix) == (Ny // 2, Nx // 2)


def test_fft2wrap_trims_even_dimensions():
    x = np.random.default_rng(0).random((12, 14))
    P, fx, fy = fft2wrap(x, 14, 12)
    assert P.shape == (11, 13)  # even dims trimmed to odd
    assert fx.shape == (13,) and fy.shape == (11,)
