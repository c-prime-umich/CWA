#!/usr/bin/env python
# Author: Timothy J. Welch
"""CWA figures (port of the plotting blocks in CWA_MATLAB/main.m).

Reproduces **Plot 4** -- "strengths of the three waves over time": a scatter of
``vdets`` / ``vcdets`` / ``vcrwps`` vs the per-block time ``ttp``, one marker
shape per wave (o / s / d), marker colour from the ``jet(100)`` palette indexed
by the wave's log-intensity normalised to ``[minI, maxI]`` (NaN -> white), with
a ``jet`` colourbar labelled ln(S).
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

__all__ = ["save_plot4_figure"]


def save_plot4_figure(plot4, run, out_path):
    """Recreate the original CWA Plot-4 figure and save a PNG to ``out_path``.

    ``plot4`` is a dict of the CWA time-resolved fields (as returned by
    ``cwa.cwa.cwa``).  Returns ``out_path`` on success, or ``None`` when
    ``maxI``/``minI`` are NaN (the original skips plotting in that case).

    The colourbar is normalised to the omit-NaN bounds ``minI``/``maxI`` (the
    same bounds the marker colours use); the reference main.m used
    ``min(intens)/max(intens)`` which is NaN for runs with missing intensities.
    """
    def g(k):
        return np.asarray(plot4[k], dtype=float).ravel()

    detins = g("detins")
    cdetins = g("cdetins")
    crwpins = g("crwpins")
    maxI = float(g("maxI")[0])
    minI = float(g("minI")[0])
    ttp = g("ttp")
    vdets = g("vdets")
    vcdets = g("vcdets")
    vcrwps = g("vcrwps")
    Ntp = int(g("Ntp")[0])

    if np.isnan(maxI) or np.isnan(minI):
        return None

    # jet(100) palette -- 100 evenly-spaced colours, the Python equivalent of
    # MATLAB's ``cmap1 = jet(100)``.
    pal = plt.get_cmap("jet")(np.linspace(0.0, 1.0, 100))  # (100, 4) RGBA

    def colors(ins):
        idx = np.ceil(99.0 * (ins - minI) / (maxI - minI)) + 1.0
        c = np.ones((Ntp, 3))  # default white for NaN/inf intensity
        ok = np.isfinite(idx)
        c[ok] = pal[np.clip(np.round(idx[ok]), 1, 100).astype(int) - 1][:, :3]
        return c

    fig, ax = plt.subplots(figsize=(10, 7))
    ax.scatter(ttp, vdets, s=40, c=colors(detins), marker="o")
    ax.scatter(ttp, vcdets, s=40, c=colors(cdetins), marker="s")
    ax.scatter(ttp, vcrwps, s=40, c=colors(crwpins), marker="d")
    ax.set_xlim(min(ttp) - 0.05, max(ttp) + 0.05)
    ax.set_ylim(-1.0, 1.0)
    ax.set_xlabel(r"$t$ [s]")
    ax.set_ylabel(r"$v/D_{CJ}$")
    ax.set_title(f"Run {run}")

    sm = plt.cm.ScalarMappable(cmap=plt.get_cmap("jet"),
                               norm=plt.Normalize(vmin=minI, vmax=maxI))
    sm.set_array([])
    cb = fig.colorbar(sm, ax=ax)
    cb.set_label(r"$\mathrm{ln}(S)$", fontsize=16)

    fig.tight_layout()
    fig.savefig(out_path, dpi=100, facecolor="w")
    plt.close(fig)
    return out_path
