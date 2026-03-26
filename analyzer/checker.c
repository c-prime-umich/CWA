#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX_WAVES 100
#define L (2.0*M_PI)

typedef struct Wave {
    double *A;
    double *sigma;
    double *v;
    int Nt;
    double theta0;
} Wave;

typedef struct Data {
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

double range2pi(double x) {
  return x - L * floor (x / L);
}

double wrap(double x) {
  return range2pi(x+L/2.0)-L/2.0;
}

double interpolate(double f, double *y, double k) {
    int j = floor(k/f);
    double frac = ((k - j*f) / f);
    // avoid accessing y[j+1] if we're at the very end where y[j+1] does not exist
    return frac>0.0 ? y[j] + frac * (y[j+1] - y[j]) : y[j];
}

double synthesize(Data *data) {
  int Nw = data->num_waves;
  int Nb = data->Nb;
  int Nfr = data->Nfr;
  int Nbg  = data->Nbg;
  double dt = data->dt;
  Wave *waves = data->waves;
  double *BG = data->BG;
  double *X = data->XT;
  double theta [ MAX_WAVES ];
  double diff_sum=0.0, energy=0.0, x;
  int w,k,i;

  for (k = 0; k < Nfr; k++) {
    for (i = 0; i < Nb; i++) {
      double a = BG[i + (int)(k*((double)(Nbg - 1)) / (Nfr - 1))*Nb];

      for (w = 0; w < Nw; w++) {
        int Nt = waves[w].Nt;
        double f = (double)(Nfr - 1) / (double)(Nt - 1);
        double A     = interpolate(f, waves[w].A, k);
        double sigma = interpolate(f, waves[w].sigma, k);

	if (k==0)
	  theta[w] = waves[w].theta0;
	else if (i==0) {
	  double v = interpolate(f, waves[w].v, k-1);
	  theta[w] = range2pi (theta[w] + v * dt);
	}
        double dx = wrap(i * (L / Nb) - theta[w]);   
        a += A * exp(-(dx*dx / (2.0 * (sigma * sigma))));
      }
      x = X[i+k*Nb];
      energy += fabs(x);
      diff_sum += fabs (x-a);
    }
  }
  return diff_sum / energy;
}

/* ======================== MAIN ======================== */

int main(int argc, char *argv[]) {

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <data_directory>\n", argv[0]);
        return 1;
    }

    const char *data_dir = argv[1];

    Data *data = load_all_data(data_dir);

    double epsilon = synthesize(data);

    printf("residual energy fraction = %.3e   (%4.1f%% of energy accounted for)\n",
	      epsilon, 100*(1-epsilon));

    return 0;
}
