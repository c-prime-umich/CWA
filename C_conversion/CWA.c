#include <stdio.h>
#include <stdlib.h>
#include <math.h>

// ------ Variables are defined for run 3433 -------

// Input Structs
typedef struct {
    double XT[101][5000];
    double fps;
    double t0[5000];
} XTStruct;

typedef struct {
    double XT[101][10001];
    double fps;
    double t0;
} XTStruct_full;

// Output Structs
typedef struct {
    double fs[101];
    double ft[4999];
    double Plight[4999][101];
    double lim2;
} Plot1;

typedef struct {
    double f_fD[2500];
    double a_Ucj[401];
    double ftp[401][2500];
} Plot2;

typedef struct {
    double a[401];
    double lights_psa[6][401];
} Plot3;

typedef struct {
    double intens[420];
    double detins[140];
    double cdetins[140];
    double crwpins[140];
    double maxI;
    double minI;
    double ttp[140];
    double vdets[140];
    double vcdets[140];
    double vcrwps[140];
    double Ntp;
} Plot4;

typedef struct {
    double ttp[140];
    double vdets[140];
    double detins[140];
    double vcdets[140];
    double cdetins[140];
    double vcrwps[140];
    double crwpins[140];
    double Ndets[140];
    double lights_t[5][301][140];
    double a_tr[301];
} PSTA;

void CWA(
    Plot1 *plot1,
    Plot2 *plot2,
    Plot3 *plot3,
    Plot4 *plot4,
    double ftpsave[402][2501],
    double PSD[11],
    PSTA *PSTA_out,
    const XTStruct *XTStruct,
    const XTStruct_full *XTStruct_full,
    const double run,
    const double phi,
    const double Dm,
    const double times[2],
    const double dat[121][12]
) {
    // ----- Basic derived parameters and checks -----

    // --- Interpolate Ucj from dat(:,0) vs dat(:,8)
    double Ucj = 0.0;
    for (int i = 0; i < 120; i++) {  // is the only way to do this to hard-code it???
        if (phi >= dat[i][0] && phi <= dat[i+1][0]) {
            double x0 = dat[i][0];
            double x1 = dat[i+1][0];
            double y0 = dat[i][8];
            double y1 = dat[i+1][8];
            Ucj = y0 + (y1 - y0)*(phi - x0)/(x1 - x0);
            break;
        }
    }

    // --- Diameter to meters
    double Cd = Dm * M_PI * 0.0254;

    // --- Non-dimensional frequency scale
    double fD = Ucj / Cd;

    // --- Read XT block from XTStruct
    double fps = XTStruct->fps;
    int Nb = 101;        // rows of XTStruct->XT
    int Nfr = 5000;      // columns of XTStruct->XT

    // --- Compute t_short array
    double t_short[5000];
    for (int i = 0; i < Nfr; i++) {
        t_short[i] = i / fps + XTStruct->t0[i];
    }

    // --- Prepare lights_short: read, transpose, and replace NaNs with 1
    double lights_short[5000][101];  // Nfr x Nb
    for (int i = 0; i < Nb; i++) {
        for (int j = 0; j < Nfr; j++) {
            double val = XTStruct->XT[i][j];
            if (isnan(val)) val = 1.0;
            lights_short[j][i] = val;  // transpose
        }
    }

    // --- Early exit on invalid input
    if (Nfr == 0 || isnan(t_short[0])) {
        for (int i = 0; i < 101; i++) {
            plot1->fs[i] = NAN;
        }
        plot1->lim2 = NAN;
        return;
    }

    // --- Limit to time window
    int ff = (int)round(1 + (fmax(t_short[0], times[0]) - t_short[0]) * fps);
    int lf = (int)round(1 + (fmin(t_short[Nfr-1], times[1]) - t_short[0]) * fps);
    if (lf > Nfr) {
        lf = Nfr;
    }
    int Nshort = lf - ff + 1;  // number of rows after window

    // --- Subset lights_short to time window and replace NaNs
    double lights_window[Nshort][101];
    for (int i = 0; i < Nshort; i++) {
        for (int j = 0; j < Nb; j++) {
            lights_window[i][j] = lights_short[ff + i][j];
        }
    }
    for (int i = 0; i < Nb; i++) {
        for (int j = 0; j < Nshort; j++) {
            if (isnan(lights_window[i][j])) lights_window[i][j] = 1.0;
        }
    }

    // free(t_short);
    // free(lights_short);
    // free(lights_window);
}

int main() {
    // --- Allocate output structs on heap ---
    Plot1 *plot1_dummy = malloc(sizeof(Plot1));
    Plot2 *plot2_dummy = malloc(sizeof(Plot2));
    Plot3 *plot3_dummy = malloc(sizeof(Plot3));
    Plot4 *plot4_dummy = malloc(sizeof(Plot4));
    PSTA  *psta_dummy = malloc(sizeof(PSTA));

    if (!plot1_dummy || !plot2_dummy || !plot3_dummy || !plot4_dummy || !psta_dummy) {
        fprintf(stderr, "Failed to allocate output structs\n");
        return 1;
    }

    // --- Allocate ftpsave on heap and initialize ---
    double (*ftpsave)[2501] = malloc(402 * sizeof(*ftpsave));
    if (!ftpsave) {
        fprintf(stderr, "Failed to allocate ftpsave\n");
        return 1;
    }
    for (int i = 0; i < 402; i++)
        for (int j = 0; j < 2501; j++)
            ftpsave[i][j] = 0.0;

    // --- Initialize PSD ---
    double PSD[11] = {0};

    // --- Initialize dat ---
    double dat[121][12] = {{0}};  // Fill with actual data if available

    // --- Initialize times and parameters ---
    double times[2] = {0.0, 1.0};
    double run = 1.0, phi = 0.5, Dm = 0.1;

    // --- Initialize XTStruct ---
    XTStruct XT_dummy;
    XTStruct_full XTf_dummy;

    XT_dummy.fps = 1000.0;
    XTf_dummy.fps = 1000.0;

    for (int i = 0; i < 101; i++) {
        for (int j = 0; j < 5000; j++) XT_dummy.XT[i][j] = 0.0;
        for (int j = 0; j < 10001; j++) XTf_dummy.XT[i][j] = 0.0;
    }

    for (int j = 0; j < 5000; j++) XT_dummy.t0[j] = 0.0;
    XTf_dummy.t0 = 0.0;

    // --- Call CWA ---
    CWA(plot1_dummy, plot2_dummy, plot3_dummy, plot4_dummy,
        ftpsave, PSD, psta_dummy,
        &XT_dummy, &XTf_dummy,
        run, phi, Dm, times, dat);

    printf("CWA compiled and ran (dummy test)\n");

    // --- Free heap memory ---
    free(plot1_dummy);
    free(plot2_dummy);
    free(plot3_dummy);
    free(plot4_dummy);
    free(psta_dummy);
    free(ftpsave);

    return 0;
}