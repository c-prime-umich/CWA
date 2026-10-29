#!/usr/bin/env python
# Author: Timothy J. Welch
"""Low-level numerical helpers ported from CWA_MATLAB.

Each function is a faithful, line-for-line translation of the corresponding
MATLAB routine so that the downstream CWA analysis reproduces the saved
ground-truth ``plot4`` struct for run 3433.

Contents
--------
arg(z)            -> CWA_MATLAB/arg.m               (polar angle in [0, 2*pi))
quadfit(x, y)     -> nested ``quadFit`` in CWA.m    (normal-equation quadratic fit)
intersect2(l1, l2)-> CWA_MATLAB/intersect2.m        (line-line intersection)
fftwrap(Hz, x)    -> CWA_MATLAB/fftwrap.m           (one-sided amplitude spectrum)
fft2wrap(x, Hzx, Hzy) -> CWA_MATLAB/fft2wrap.m      (shifted 2D FFT + freq axes)
"""
import numpy as np

__all__ = ["arg", "quadfit", "intersect2", "fftwrap", "fft2wrap"]


def arg(z):
    """Polar angle of complex ``z`` in radians, in [0, 2*pi).

    Port of CWA_MATLAB/arg.m.  The reference implementation initialises the
    result to the real part and only overwrites it for the four strict quadrant
    cases; that behaviour (including the degenerate x<0, y==0 case) is preserved
    here for fidelity.
    """
    zin = np.asarray(z, dtype=complex)
    scalar = zin.ndim == 0
    shape = zin.shape
    z = zin.ravel()
    x = z.real
    y = z.imag
    phi = x.copy()
    with np.errstate(divide="ignore", invalid="ignore"):
        atan = np.arctan(y / x)

    phi[(x >= 0) & (y >= 0)] = atan[(x >= 0) & (y >= 0)]
    phi[(x >= 0) & (y < 0)] = atan[(x >= 0) & (y < 0)] + 2 * np.pi
    phi[(x < 0) & (y > 0)] = atan[(x < 0) & (y > 0)] + np.pi
    phi[(x < 0) & (y < 0)] = atan[(x < 0) & (y < 0)] + np.pi

    return phi[0] if scalar else phi.reshape(shape)


def quadfit(x, y):
    """Quadratic fit ``y ~= a*x^2 + b*x + c`` via normal equations.

    Port of the nested ``quadFit`` in CWA.m.  Returns ``[a, b, c]``.
    """
    x = np.asarray(x, dtype=float).ravel()
    y = np.asarray(y, dtype=float).ravel()
    A = np.array([
        [np.sum(x**4), np.sum(x**3), np.sum(x**2)],
        [np.sum(x**3), np.sum(x**2), np.sum(x)],
        [np.sum(x**2), np.sum(x), float(len(x))],
    ])
    B = np.array([np.sum(x**2 * y), np.sum(x * y), np.sum(y)])
    return np.linalg.solve(A, B)


def intersect2(l1, l2):
    """Intersection of two lines given in [x0, y0, xhat, yhat] form.

    Port of CWA_MATLAB/intersect2.m (point-slope / unit-vector lines).
    """
    l1 = np.asarray(l1, dtype=float).ravel()
    l2 = np.asarray(l2, dtype=float).ravel()
    k = (l1[0] - l2[0] + l1[2] * (l2[1] - l1[1]) / l1[3]) / (l2[2] - l1[2] * l2[3] / l1[3])
    x = l2[0] + k * l2[2]
    y = l2[1] + k * l2[3]
    return x, y


def fftwrap(Hz, xIn, nargout=3):
    """One-sided Fourier amplitude spectrum.

    Port of CWA_MATLAB/fftwrap.m.

    Parameters
    ----------
    Hz : float        sampling rate
    xIn : array       1-D signal or 2-D (rows=time, cols=sensors)
    nargout : int     number of outputs requested (mirrors MATLAB ``nargout``):
                      1 -> (f,), 2 -> (f, P), 3 -> (f, P, phi)

    Returns
    -------
    f   : (L/2+1,)      frequency axis  Hz*(0:L/2)/L  (L after even-trim)
    P   : (L/2+1, Nc)   one-sided amplitude spectrum (interior bins doubled)
    phi : (L/2+1, Nc)   phase (only when nargout >= 3)
    """
    xIn = np.asarray(xIn, dtype=float)
    if xIn.ndim == 1:
        xIn = xIn.reshape(-1, 1)  # a bare 1-D vector is a column, as in MATLAB
    Nrow, Ncol = xIn.shape

    if Nrow == 1 or Ncol == 1:
        x = xIn.reshape(-1, 1) if Nrow < Ncol else xIn
        L = x.shape[0]
        if L % 2 == 1:
            x = x[0:L - 1, :]
            L = x.shape[0]
    else:
        L = Nrow
        if L % 2 == 1:
            x = xIn[0:L - 1, :]
            L = L - 1
        else:
            x = xIn

    f = Hz * np.arange(L // 2 + 1) / L
    if nargout == 1:
        return f

    y = np.fft.fft(x, axis=0)
    P2 = np.abs(y) / L
    P = P2[0:L // 2 + 1, :]
    P[1:L // 2, :] = 2 * P[1:L // 2, :]

    if nargout >= 3:
        phi = arg(y)[0:L // 2 + 1, :]
        return f, P, phi
    return f, P


def fft2wrap(x, Hzx, Hzy):
    """Shifted 2-D FFT with frequency axes.

    Port of CWA_MATLAB/fft2wrap.m.  Even dimensions are trimmed to odd before
    the transform so that the fftshifted grid is centred on zero.

    Returns (P, fx, fy) where P is the raw (complex) shifted 2-D FFT.
    """
    x = np.asarray(x, dtype=float)
    Ny, Nx = x.shape
    if Nx % 2 == 0:
        x = x[:, 0:Nx - 1]
        Nx = Nx - 1
    if Ny % 2 == 0:
        x = x[0:Ny - 1, :]
        Ny = Ny - 1
    fx = Hzx * np.arange(-(Nx - 1) // 2, (Nx - 1) // 2 + 1) / Nx
    fy = Hzy * np.arange(-(Ny - 1) // 2, (Ny - 1) // 2 + 1) / Ny
    P = np.fft.fftshift(np.fft.fft2(x))
    return P, fx, fy
