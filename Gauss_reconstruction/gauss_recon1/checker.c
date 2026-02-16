/*
 * XT Recreation Checker (C version)
 *
 * Author: Timothy J. Welch
 *
 * This program:
 *  - Loads XT and XT_syn from text files
 *  - Computes L1 norm of difference
 *  - Optionally prints epsilon
 *
 * Usage:
 *   ./checker XT.txt XT_syn.txt 1
 *
 *   Third argument (optional):
 *     1 -> verbose on
 *     0 -> verbose off
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double compute_l1(const char *file1, const char *file2) {
    FILE *f1 = fopen(file1, "r");
    FILE *f2 = fopen(file2, "r");

    if (!f1 || !f2) {
        fprintf(stderr, "Error opening input files.\n");
        exit(EXIT_FAILURE);
    }

    double x1, x2;
    double epsilon = 0.0;

    while (1) {
        int r1 = fscanf(f1, "%lf", &x1);
        int r2 = fscanf(f2, "%lf", &x2);

        if (r1 == EOF || r2 == EOF)
            break;

        if (r1 != 1 || r2 != 1) {
            fprintf(stderr, "File read error.\n");
            exit(EXIT_FAILURE);
        }

        epsilon += fabs(x2 - x1);
    }

    fclose(f1);
    fclose(f2);

    return epsilon;
}

int main(int argc, char *argv[]) {

    if (argc < 3) {
        printf("Usage: %s XT.txt XT_syn.txt [VERBOSE]\n", argv[0]);
        return 1;
    }

    int VERBOSE = 0;
    if (argc >= 4)
        VERBOSE = atoi(argv[3]);

    double ep = compute_l1(argv[1], argv[2]);

    if (VERBOSE) {
        printf("epsilon = %.3e\n", ep);
    }

    return 0;
}
