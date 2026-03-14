#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_WAVES 100
#define MAX_LINE 10000
#define L (2.0*M_PI)

typedef struct {
    double *A;
    double *sigma;
    double *v;
    double *t;
    int Nt;
    double theta0;
} Wave;

typedef struct {
    double *XT;
    double *XT_bg;
    int Nb;
    int Nfr;
    Wave waves[MAX_WAVES];
    int num_waves;
} Data;

/* ======================== Utility Functions ======================== */

double wrap(double x) {
    return fmod(fmod(x + L/2.0, L) + L, L) - L/2.0;
}

double mod_positive(double x) {
    double r = fmod(x, L);
    return (r < 0) ? r + L : r;
}

double interp1(double *x, double *y, int n, double xi) {
    if (xi <= x[0]) return y[0];
    if (xi >= x[n-1]) return y[n-1];

    for (int i = 0; i < n-1; i++) {
        if (xi >= x[i] && xi <= x[i+1]) {
            double t = (xi - x[i]) / (x[i+1] - x[i]);
            return y[i] + t * (y[i+1] - y[i]);
        }
    }
    return 0.0;
}

/* ======================== CSV Readers ======================== */

double* read_csv_flat(const char *filename, int *rows, int *cols)
{
    FILE *fp = fopen(filename, "r");
    if (!fp) {
        perror("Failed to open file");
        exit(1);
    }

    char *line = NULL;
    size_t len = 0;
    ssize_t read;

    int r = 0;
    int c = -1;
    int capacity = 1024;
    int count = 0;

    double *row_major = malloc(capacity * sizeof(double));

    // --- Read row-wise first ---
    while ((read = getline(&line, &len, fp)) != -1) {

        int current_cols = 0;
        char *token = strtok(line, ",\n\r");

        while (token) {

            if (count >= capacity) {
                capacity *= 2;
                row_major = realloc(row_major, capacity * sizeof(double));
            }

            row_major[count++] = atof(token);
            current_cols++;
            token = strtok(NULL, ",\n\r");
        }

        if (c == -1)
            c = current_cols;
        else if (current_cols != c) {
            printf("ERROR: Inconsistent column count in %s\n", filename);
            printf("Expected %d columns, got %d\n", c, current_cols);
            exit(1);
        }

        r++;
    }

    free(line);
    fclose(fp);

    *rows = r;
    *cols = c;

    // --- Allocate column-major array ---
    double *col_major = malloc(r * c * sizeof(double));

    // Convert row-major → column-major
    for (int i = 0; i < r; i++) {
        for (int j = 0; j < c; j++) {
            col_major[j*r + i] = row_major[i*c + j];
        }
    }

    free(row_major);

    return col_major;
}

double* read_csv_vector(const char *filename, int *n)
{
    int rows, cols;
    double *data = read_csv_flat(filename, &rows, &cols);

    if (rows != 1 && cols != 1) {
        printf("ERROR: %s is not a vector (got %d x %d)\n",
               filename, rows, cols);
        exit(1);
    }

    *n = rows * cols;
    return data;
}

/* ======================== FUNCTION 1 ======================== */
/* Load all data */

Data* load_all_data() {

    Data *data = malloc(sizeof(Data));

    int rows, cols;

    /* Load XT */
    data->XT = read_csv_flat("data/XT.csv", &rows, &cols);
    data->Nb = rows;
    data->Nfr = cols;

    /* Load background */
    int r2, c2;
    data->XT_bg = read_csv_flat("data/XT_bg.csv", &r2, &c2);

    printf("XT size:     %d x %d = %d elements\n",
       data->Nb, data->Nfr, data->Nb * data->Nfr);

    printf("XT_bg size:  %d x %d = %d elements\n",
        r2, c2, r2 * c2);

    data->num_waves = 0;

    /* Load waves */
    for (int i = 1; i <= MAX_WAVES; i++) {

        char path[256];
        snprintf(path, sizeof(path), "data/wave_%d/A.csv", i);

        FILE *fp = fopen(path, "r");
        if (!fp) break;
        fclose(fp);

        Wave *w = &data->waves[data->num_waves];

        snprintf(path, sizeof(path), "data/wave_%d/A.csv", i);
        w->A = read_csv_vector(path, &w->Nt);

        snprintf(path, sizeof(path), "data/wave_%d/sigma.csv", i);
        w->sigma = read_csv_vector(path, &w->Nt);

        snprintf(path, sizeof(path), "data/wave_%d/v.csv", i);
        w->v = read_csv_vector(path, &w->Nt);

        snprintf(path, sizeof(path), "data/wave_%d/t.csv", i);
        w->t = read_csv_vector(path, &w->Nt);

        snprintf(path, sizeof(path), "data/wave_%d/theta0.csv", i);
        int dummy;
        double *tmp = read_csv_vector(path, &dummy);
        w->theta0 = tmp[0];
        free(tmp);

        data->num_waves++;
    }

    return data;
}

/* ======================== FUNCTION 2 ======================== */
/* Compute epsilon */

double compute_epsilon(Data *data) {

    int Nb = data->Nb;
    int Nfr = data->Nfr;

    double *XT_syn = malloc(Nb * Nfr * sizeof(double));
    memcpy(XT_syn, data->XT_bg, Nb * Nfr * sizeof(double));

    double dth = 2.0 * M_PI / Nb;

    /* theta grid */
    double *theta = malloc(Nb * sizeof(double));
    for (int i = 0; i < Nb; i++)
        theta[i] = i * dth;

    /* Loop over waves */
    for (int w = 0; w < data->num_waves; w++) {

        Wave *wave = &data->waves[w];

        double t_start = wave->t[0];
        double t_end   = wave->t[wave->Nt - 1];

        double *t_full = malloc(Nfr * sizeof(double));
        for (int i = 0; i < Nfr; i++)
            t_full[i] = t_start + (t_end - t_start) * i / (Nfr - 1);

        double dt = t_full[1] - t_full[0];

        double theta0 = wave->theta0;

        /* Initial frame */
        for (int i = 0; i < Nb; i++) {
            double dx = wrap(theta[i] - theta0);
            XT_syn[i] += wave->A[0] *
                exp(-dx*dx / (2.0 * wave->sigma[0] * wave->sigma[0]));
        }

        /* Time loop */
        for (int it = 1; it < Nfr; it++) {

            double A_it     = interp1(wave->t, wave->A, wave->Nt, t_full[it]);
            double sigma_it = interp1(wave->t, wave->sigma, wave->Nt, t_full[it]);
            double v_it     = interp1(wave->t, wave->v, wave->Nt, t_full[it]);

            theta0 += v_it * dt;
            theta0 = mod_positive(theta0);

            for (int i = 0; i < Nb; i++) {
                double dx = wrap(theta[i] - theta0);
                XT_syn[i + it*Nb] +=
                    A_it * exp(-dx*dx / (2.0 * sigma_it * sigma_it));
            }
        }

        free(t_full);
    }

    /* Compute epsilon */
    double XT_energy = 0.0;
    double diff_sum = 0.0;

    for (int i = 0; i < Nb * Nfr; i++) {
        XT_energy += fabs(data->XT[i]);
        diff_sum  += fabs(XT_syn[i] - data->XT[i]);
    }

    free(XT_syn);
    free(theta);

    double epsilon = diff_sum / XT_energy;

    return epsilon;
}

/* ======================== MAIN ======================== */

int main() {

    Data *data = load_all_data();

    double epsilon_print = compute_epsilon(data);

    printf("residual energy fraction = %.3e\n", epsilon_print);

    return 0;
}