#!/usr/bin/env python
# Author: Timothy J. Welch
"""Reference figures for the synthesis (port of the plotting blocks in
Gauss_Syn_Runner.m).  Nine PNGs are written under ``out_dir``:

  fig1_original_XT.png          imagesc of the original (uncleaned) XT + strip
  fig2_xt_subtraction.png       imagesc of the removed background (XT - cleaned)
  fig3_cleaned_XT.png           imagesc of the cleaned diagram + full-time strip
  fig4_syn_XT.png               imagesc of the synthetic diagram + strip
  fig5_diff_XT.png              imagesc of (cleaned - synthetic) + strip
  fig6_slice.png                sensor-60 slice: data vs recreation (3 frames)
  fig7_slice_subtraction.png    sensor-60 slice: data vs (data - synthetic)
  fig8_cleared_subtraction.png  sensor-60 slice: data vs (cleaned - 100*synthetic)
  fig9_A_theta.png              four theta profiles: data vs recreation

``pcolormesh`` is used in place of ``imagesc`` (equivalent cell grid).  Axis
limits, titles and legends follow the MATLAB source.  The figure title is
derived from ``run`` (falling back to the ``run<N>`` output-directory name) so
the plots are labelled correctly for any run, not just 3433.

  Every x-t *diagram* (figs 1, 2, 3, 4, 5) carries a colorbar and shares one
common amplitude scale -- the min/max over all of them for that run -- so the
plots are directly comparable.  The bounds differ run-to-run but are identical
plot-to-plot within a run.

With ``movie=True``, each x-t diagram also writes an animated ``<name>.mp4``
(ffmpeg present) or ``<name>.gif`` (Pillow) in which the magnified window slides
across the full time series, so the whole record can be watched.
"""
import os
import re

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

__all__ = ["save_all_figures"]


def _panel(fig, pos, x, y, Z, xlim, ylim, vmin, vmax, red_lines=(),
           colorbar_cax=None):
    ax = fig.add_axes(pos)
    im = ax.pcolormesh(x, y, Z, shading="auto", vmin=vmin, vmax=vmax)
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_yticks([])
    for xr in red_lines:
        ax.axvline(xr, color="r", lw=3)
    if colorbar_cax is not None:
        fig.colorbar(im, cax=colorbar_cax)
    return ax


def _diagram_figure(path, title, x, y, Z, x_strip, xlim_top, xlim_strip,
                    red_lines, ymax, vmin, vmax):
    fig = plt.figure(figsize=(25, 6))
    # main (top) panel, with a reserved colorbar slot to its right
    cax = fig.add_axes([0.865, 0.3, 0.02, 0.6])
    ax = _panel(fig, [0.1, 0.3, 0.75, 0.6], x, y, Z, xlim_top, (0, ymax),
                vmin, vmax, red_lines=(), colorbar_cax=cax)
    ax.set_title(title)
    ax.set_xlabel("Time [s]")
    ax.set_ylabel(r"$\theta$")
    # full-time strip, same shared scale, aligned under the main panel
    _panel(fig, [0.1, 0.12, 0.75, 0.03], x_strip, y, Z, xlim_strip, (0, ymax),
           vmin, vmax, red_lines=red_lines)
    fig.savefig(path, dpi=100, facecolor="w")
    plt.close(fig)


def _diagram_movie(base, title, t, thetap, Z, vmin, vmax, win_frames=300):
    """Movie of the magnified window sliding across the full time series.

    The movie is written as ``base + ".mp4"`` (via ``ffmpeg``).  If no ``ffmpeg``
    binary is present it falls back to ``base + ".gif"`` (Pillow) and emits a
    loud warning, so the format never silently downgrades.  The top panel's time
    window, and the two red markers on the full-time strip, advance frame by
    frame from the start to the end of the record so the whole series can be
    watched magnified.  Returns the extension that was written.

    ``imshow`` (not ``pcolormesh``) is used for speed; the data is dense so the
    two render identically at this scale.
    """
    import shutil
    import warnings
    from matplotlib import animation

    Nfr = t.size
    ymax = float(thetap.max())
    has_ff = shutil.which("ffmpeg") is not None
    n_frames = 150 if has_ff else 60
    fps = 24 if has_ff else 12
    dpi = 100 if has_ff else 50
    extent = (float(t[0]), float(t[-1]), 0.0, ymax)
    span = max(Nfr - win_frames, 1)
    starts = np.linspace(0, span, n_frames).round().astype(int)

    fig = plt.figure(figsize=(25, 6), dpi=dpi)
    ax = fig.add_axes([0.1, 0.3, 0.75, 0.6])
    im = ax.imshow(Z, extent=extent, origin="lower", aspect="auto",
                   vmin=vmin, vmax=vmax)
    ax.set_yticks([])
    ax.set_title(title)
    ax.set_xlabel("Time [s]")
    ax.set_ylabel(r"$\theta$")
    ax.set_xlim(extent[0], t[min(win_frames, Nfr - 1)])
    cax = fig.add_axes([0.865, 0.3, 0.02, 0.6])
    fig.colorbar(im, cax=cax)

    ax2 = fig.add_axes([0.1, 0.12, 0.75, 0.03])
    ax2.imshow(Z, extent=extent, origin="lower", aspect="auto",
               vmin=vmin, vmax=vmax)
    ax2.set_yticks([])
    ax2.set_xlim(extent[0], extent[1])
    la = ax2.axvline(t[0], color="r", lw=3)
    lb = ax2.axvline(t[min(win_frames, Nfr - 1)], color="r", lw=3)

    def update(i):
        s = int(starts[i]); e = min(s + win_frames, Nfr - 1)
        ax.set_xlim(t[s], t[e])
        la.set_xdata([t[s], t[s]])
        lb.set_xdata([t[e], t[e]])
        return la, lb

    anim = animation.FuncAnimation(fig, update, frames=n_frames, blit=False)
    if has_ff:
        anim.save(base + ".mp4",
                  writer=animation.FFMpegWriter(fps=fps, bitrate=8000))
        ext = ".mp4"
    else:
        warnings.warn(f"ffmpeg not found -- movie {os.path.basename(base)} "
                      "written as .gif fallback (install ffmpeg for .mp4).")
        anim.save(base + ".gif", writer=animation.PillowWriter(fps=fps))
        ext = ".gif"
    plt.close(fig)
    return ext


def _slice_figure(path, t, curve_data, curve_other, label_other, win_frames):
    Nfr = t.size
    T = t[-1] - t[0]
    lims = [
        (t[0], t[0] + win_frames * T / Nfr),
        (t[Nfr // 2], t[Nfr // 2] + win_frames * T / Nfr),
        (t[-1] - win_frames * T / Nfr, t[-1]),
    ]
    fig, axes = plt.subplots(1, 3, figsize=(25, 6))
    for ax, (lo, hi) in zip(axes, lims):
        m = (t >= lo) & (t <= hi)
        ax.plot(t[m], curve_data[m], lw=2, label="XT Data")
        ax.plot(t[m], curve_other[m], lw=2, label=label_other)
        ax.set_xlim(lo, hi)
        ax.set_xlabel("Time [s]")
        ax.set_ylabel("Amplitude")
        ax.legend()
    fig.savefig(path, dpi=100, facecolor="w")
    plt.close(fig)


def save_all_figures(t, fps, thetap, XT, XT_cleaned, XT_syn, XT_subtraction,
                     out_dir, win=20, run=None, movie=False):
    Nfr = t.size
    ymax = thetap.max()
    if run is None:
        m = re.search(r"run(\d+)", os.path.basename(out_dir))
        run = m.group(1) if m else ""
    title = f"Run {run}" if run else "XT Diagram"
    red = (t[0], t[300])
    strip_xlim = (t[0], t[-1])

    # The five x-t diagrams.  They share one color scale (vmin, vmax) taken
    # from the min/max over all of them so nothing is clipped; bounds differ
    # run-to-run but are identical plot-to-plot.
    diagrams = [
        ("fig1_original_XT", XT),
        ("fig2_xt_subtraction", XT_subtraction),
        ("fig3_cleaned_XT", XT_cleaned),
        ("fig4_syn_XT", XT_syn),
        ("fig5_diff_XT", XT_cleaned - XT_syn),
    ]
    vmin = float(min(Z.min() for _, Z in diagrams))
    vmax = float(max(Z.max() for _, Z in diagrams))

    for name, Z in diagrams:
        _diagram_figure(os.path.join(out_dir, f"{name}.png"), title,
                        t, thetap, Z, t, (t[0], t[0] + 300 / fps),
                        strip_xlim, red, ymax, vmin, vmax)
        if movie:
            ext = _diagram_movie(os.path.join(out_dir, name), title, t, thetap,
                                 Z, vmin, vmax, win_frames=300)
            print(f"   movie: {name}{ext}", flush=True)

    s60 = 59  # MATLAB row 60 (1-based)
    # 6. slice: data vs recreation
    _slice_figure(os.path.join(out_dir, "fig6_slice.png"), t,
                  XT_cleaned[s60], XT_syn[s60], "Recreation", 100)
    # 7. slice: data vs subtraction
    _slice_figure(os.path.join(out_dir, "fig7_slice_subtraction.png"), t,
                  XT_cleaned[s60], XT_cleaned[s60] - XT_syn[s60], "Subtraction", 100)
    # 8. cleared: data vs (cleaned - 100*synthetic)
    XT_cleared = (XT_cleaned - 100.0 * XT_syn)
    XT_cleared[XT_cleared < 0] = 0
    _slice_figure(os.path.join(out_dir, "fig8_cleared_subtraction.png"), t,
                  XT_cleaned[s60], XT_cleared[s60], "Cleared", 100)

    # 9. A-theta: four profiles data vs recreation
    fig, axes = plt.subplots(2, 2, figsize=(25, 6))
    for ax, k in zip(axes.ravel(),
                     [0, Nfr // 4, 2 * (Nfr // 4), 3 * (Nfr // 4)]):
        ax.plot(thetap, XT_cleaned[:, k], lw=3, label="XT Data")
        ax.plot(thetap, XT_syn[:, k], lw=3, label="Recreation")
        ax.set_xlabel("Theta [rad]")
        ax.set_ylabel("Amplitude")
        ax.legend()
    fig.savefig(os.path.join(out_dir, "fig9_A_theta.png"), dpi=100, facecolor="w")
    plt.close(fig)
