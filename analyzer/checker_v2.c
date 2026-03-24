#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_WAVES 100
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
    double *BG;
    int Nb;
    int Nfr;
    int Nbg;
    double dt;
    Wave waves[MAX_WAVES];
    int num_waves;
} Data;

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

Data* load_all_data(const char *dir) {

    Data *data = malloc(sizeof(Data));

    int rows, cols;

    char path[512];

    /* Load XT */
    snprintf(path, sizeof(path), "%s/XT.csv", dir);
    data->XT = read_csv_flat(path, &rows, &cols);
    data->Nb = rows;
    data->Nfr = cols;

    /* Load background */
    int r2, c2;
    snprintf(path, sizeof(path), "%s/BG.csv", dir);
    data->BG = read_csv_flat(path, &r2, &c2);
    data->Nbg = c2;

    /* Load dt */
    int r_dt, c_dt;
    snprintf(path, sizeof(path), "%s/dt.csv", dir);

    double *tmp = read_csv_flat(path, &r_dt, &c_dt);

    if (r_dt * c_dt != 1) {
        fprintf(stderr, "dt.csv must contain exactly one value\n");
        exit(EXIT_FAILURE);
    }

    data->dt = tmp[0];
    free(tmp);

    data->num_waves = 0;

    /* Load waves */
    for (int i = 1; i <= MAX_WAVES; i++) {

        snprintf(path, sizeof(path), "%s/wave_%d/A.csv", dir, i);

        FILE *fp = fopen(path, "r");
        if (!fp) break;
        fclose(fp);

        Wave *w = &data->waves[data->num_waves];
	int Nt;

        snprintf(path, sizeof(path), "%s/wave_%d/A.csv", dir, i);
        w->A = read_csv_vector(path, &w->Nt);

        snprintf(path, sizeof(path), "%s/wave_%d/sigma.csv", dir, i);
        w->sigma = read_csv_vector(path, &Nt);
	if (Nt != w->Nt) {
	  fprintf(stderr, "Wave %d, A vector has %d values but sigma vector has %d values\n",i,w->Nt,Nt);
	  exit(EXIT_FAILURE);
	}

        snprintf(path, sizeof(path), "%s/wave_%d/v.csv", dir, i);
        w->v = read_csv_vector(path, &w->Nt);
	if (Nt != w->Nt) {
	  fprintf(stderr, "Wave %d, A vector has %d values but v vector has %d values\n",i,w->Nt,Nt);
	  exit(EXIT_FAILURE);
	}

        /* Create time vector */
        w->t = malloc(w->Nt * sizeof(double));
        double dt_dummy = (double)(data->Nfr - 1) / (double)(w->Nt - 1);
        for (int k = 0; k < w->Nt; k++) {
            w->t[k] = k * dt_dummy;
        }

        snprintf(path, sizeof(path), "%s/wave_%d/theta0.csv", dir, i);
        int dummy;
        double *tmp = read_csv_vector(path, &dummy);
        w->theta0 = tmp[0];
        free(tmp);

        data->num_waves++;
    }

    return data;
}

/* ======================== FUNCTION 2 ======================== */

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

void synthesize_orig(Data *data, double *XT_syn) {
  int Nb = data->Nb;
  int Nfr = data->Nfr;
  int Nbg  = data->Nbg;

  /* interpolate XT_bg from BG */
  double *XT_bg = malloc(Nb * Nfr * sizeof(double));
  double scale = (double)(Nbg - 1) / (Nfr - 1);
  for (int k = 0; k < Nfr; k++) {
    int j = (int)(k * scale);   // floor
    for (int i = 0; i < Nb; i++) {
      XT_bg[i + k*Nb] = data->BG[i + j*Nb];
    }
  }

  memcpy(XT_syn, XT_bg, Nb * Nfr * sizeof(double));

  double dth = 2.0 * M_PI / Nb;

  /* theta grid */
  double *theta = malloc(Nb * sizeof(double));
  for (int i = 0; i < Nb; i++)
    theta[i] = i * dth;

  /* Loop over waves */
  for (int w = 0; w < data->num_waves; w++) {

    Wave *wave = &data->waves[w];

    /* Make time array */
    double dt = 1;

    double theta0 = wave->theta0;

    /* Initial frame */
    for (int i = 0; i < Nb; i++) {
      double dx = wrap(theta[i] - theta0);
      XT_syn[i] += wave->A[0] *
	exp(-dx*dx / (2.0 * wave->sigma[0] * wave->sigma[0]));
    }

    /* Time loop */
    for (int it = 1; it < Nfr; it++) {
      double A_it     = interp1(wave->t, wave->A, wave->Nt, (double)it);
      double sigma_it = interp1(wave->t, wave->sigma, wave->Nt, (double)it);
      double v_it     = interp1(wave->t, wave->v, wave->Nt, (double)(it-1));

      theta0 += v_it * data->dt;
      theta0 = mod_positive(theta0);

      for (int i = 0; i < Nb; i++) {
	double dx = wrap(theta[i] - theta0);
	XT_syn[i + it*Nb] +=
	  A_it * exp(-dx*dx / (2.0 * sigma_it * sigma_it));
      }
    }
  }
  free(theta);

}

double range2pi(double x) {
  return x - L * floor (x / L);
}

double wrap_new(double x) {
  return range2pi(x+L/2.0)-L/2.0;
}

double interpolate(double f, double *y, int n, double k) {
    int j = floor(k/f);
    return y[j] + ((k - j*f) / f) * (y[j+1] - y[j]);
}

void synthesize(Data *data, double *S) {
  int Nw = data->num_waves;
  int Nb = data->Nb;
  int Nfr = data->Nfr;
  int Nbg  = data->Nbg;
  double dt = data->dt;
  Wave *waves = data->waves;
  double theta [ MAX_WAVES ];
  int w,k,i;

  for (k = 0; k < Nfr; k++) {
    for (i = 0; i < Nb; i++) {
      double a = data->BG[i + (int)(k*((double)(Nbg - 1)) / (Nfr - 1))*Nb];

      for (w = 0; w < Nw; w++) {
        int Nt = waves[w].Nt;
        double f = (double)(Nfr - 1) / (double)(Nt - 1);
        double A     = interpolate(f, waves[w].A, Nt, k);
        double sigma = interpolate(f, waves[w].sigma, Nt, k);

	if (k==0)
	  theta[w] = waves[w].theta0;
	else if (i==0) {
	  double v = interpolate(f, waves[w].v, Nt, k-1);
	  theta[w] = range2pi (theta[w] + v * dt);
	}

        double dx = wrap_new(i * (L / Nb) - theta[w]);   
        a += A * exp(-dx*dx / (2.0 * sigma * sigma));
      }
      S[i + k*Nb] = a;
    }
  }
}

double compute_epsilon(Data *data) {
    int Nb = data->Nb;
    int Nfr = data->Nfr;
    int Nbg  = data->Nbg;
    double *XT_syn_orig = malloc(Nb * Nfr * sizeof(double));
    double *XT_syn = malloc(Nb * Nfr * sizeof(double));

    synthesize_orig(data, XT_syn_orig);
    synthesize(data, XT_syn);

    /* Check that synthesize is the same as synthesize_orig */
    double error = 0.0;
    for (int i = 0; i < Nb*Nfr; i++) {
      error += fabs (XT_syn[i] - XT_syn_orig[i]);
    }
    printf ("algorithm error check: total %f,  average %g\n", error, error / (Nb*Nfr));

    /* Compute epsilon */
    double XT_energy = 0.0;
    double diff_sum = 0.0;

    for (int i = 0; i < Nb * Nfr; i++) {
      diff_sum  += fabs(XT_syn[i] - data->XT[i]);
      XT_energy += fabs(data->XT[i]);
    }

    free(XT_syn);

    double epsilon = diff_sum / XT_energy;

    return epsilon;
}

/* ======================== MAIN ======================== */

int main(int argc, char *argv[]) {

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <data_directory>\n", argv[0]);
        return 1;
    }

    const char *data_dir = argv[1];

    Data *data = load_all_data(data_dir);

    double epsilon_print = compute_epsilon(data);

    printf("residual energy fraction = %.3e   (%4.1f%% of energy accounted for)\n",
	      epsilon_print, 100*(1-epsilon_print));

    return 0;
}
