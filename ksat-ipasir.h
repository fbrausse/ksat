
#ifndef KSAT_IPASIR_H
#define KSAT_IPASIR_H

#ifdef __cplusplus
extern "C" {
#endif

const char * ksat_ipasir_signature    ();
void *       ksat_ipasir_init         ();
void         ksat_ipasir_release      (void *solver);
void         ksat_ipasir_add          (void *solver, int lit_or_zero);
void         ksat_ipasir_assume       (void *solver, int lit);
int          ksat_ipasir_solve        (void *solver);
int          ksat_ipasir_val          (void *solver, int lit);
void         ksat_ipasir_set_terminate(void *solver, void *state,
                                       int (*terminate)(void *state));

// int          ksat_ipasir_failed       (void *solver, int lit);

#ifdef __cplusplus
}
#endif

#endif
