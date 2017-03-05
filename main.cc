
#include <cstdio>
#include <cstring>
#include <cctype>
#include <unistd.h>

#include "ksat.hh"

using namespace ksat_ns;

static int read_dimacs(ksat &solver, FILE *in)
{
	char *line = nullptr;
	size_t sz = 0;
	ssize_t rd;
	enum { HEADER, BODY } state = HEADER;
	unsigned long nv, nc, actual_nc = 0;
	std::vector<lit> clause;
	for (unsigned no=0; (rd = getline(&line, &sz, in)) > 0; no++) {
		while (rd && iscntrl(line[rd-1]))
			line[--rd] = '\0';
		if (!rd) {
			fprintf(stderr,
			        "warning: skipping empty input line %u\n",no+1);
			continue;
		}
		if (line[0] == 'c')
			continue;
		char *tok, *endptr;
		if (isspace(line[1])) {
			switch (line[0]) {
			case 'c':
				continue;
			case 'p':
				if (state != HEADER) {
					fprintf(stderr,
						"error: duplicate header on line %u\n",
						no+1);
					return -1;
				}
				if (sscanf(line, "p cnf %lu %lu", &nv, &nc) != 2)
					goto error_line;
				if (nv >= 1U << LOG_NUM_VARS) {
					fprintf(stderr, "error: cannot handle "
					                ">= 2**%u variables\n",
					        LOG_NUM_VARS);
					return -1;
				}
				state = BODY;
				solver.init(nv);
				continue;
			}
		}
		if (state == BODY) {
			int zero = -1;
			for (tok = strtok(line, " \t"); tok; tok = strtok(NULL, " \t")) {
				if (zero >= 0) {
					fprintf(stderr,
					        "error: clause on input line "
					        "%u not zero-terminated\n",
					        no+1);
					return -1;
				}
				long v = strtol(tok, &endptr, 10);
				if (*endptr)
					goto error_line;
				if ((unsigned long)std::abs(v) > nv) {
					fprintf(stderr,
					        "error: invalid literal '%s' "
					        "in clause on input line %u: "
					        "variable out of range\n",
					        tok, no+1);
					return -1;
				}
				if (!v)
					zero = clause.size();
				else
					clause.push_back(dimacs_to_lit(v));
			}
			if (zero != (ssize_t)clause.size()) {
				fprintf(stderr,
				        "error: clause on input line "
				        "%u not zero-terminated\n",
				        no+1);
				return -1;
			}
			if (!clause.empty()) {
				solver.add_clause(clause);
				actual_nc++;
				clause.clear();
			}
			continue;
		}
error_line:
		fprintf(stderr,
		        "error: input line %u is not DIMACS CNF format\n",
		        no+1);
		return -1;
	}
	free(line);
	if (state != BODY) {
		fprintf(stderr, "error: header missing\n");
		return -1;
	}
	if (nc != actual_nc)
		fprintf(stderr, "warning: number of clauses in header wrong "
		                "(%lu vs. actual %lu)\n",
		        nc, actual_nc);
	return 0;
}

static void do_dump(const ksat &solver, FILE *f)
{
	unsigned long n = 0;
	for (const auto &c : solver.clauses())
		for (lit l : c) {
			if (solver.get_assign(var(l)) & (1U << sign(l)))
				break;
			if (solver.get_assign(var(l)))
				continue;
			n++;
			break;
		}
	fprintf(f, "c unsat:%d\n", solver.is_unsat());
	fprintf(f, "p cnf %u %lu\n", solver.num_vars(), n + solver.units_size());
#if 1
	for (auto it = solver.units_begin(); it != solver.units_end(); ++it)
		fprintf(f, "%ld 0\n", lit_to_dimacs(it->implied_lit));
#endif
	std::vector<lit> cl;
	for (const auto &c : solver.clauses()) {
		cl.clear();
		for (lit l : c) {
			if (solver.get_assign(var(l)) & (1U << sign(l)))
				goto next;
			if (solver.get_assign(var(l)))
				continue;
			cl.push_back(l);
		}
		if (!cl.empty()) {
			for (lit l : cl)
				fprintf(f, "%ld ", lit_to_dimacs(l));
			fprintf(f, "0\n");
		}
	next:;
	}
}

#define USAGE	"usage: %s [-OPTS] [INSTANCE.cnf]\n"

int verbosity = 0;

int main(int argc, char **argv)
{
	FILE *dump = NULL;
	ksat solver;
	int opt;

	while ((opt = getopt(argc, argv, ":d:hr:v")) != -1)
		switch (opt) {
		case 'd':
			if (!(dump = fopen(optarg, "w"))) {
				perror(optarg);
				exit(1);
			}
			break;
		case 'h':
			fprintf(stderr, USAGE, argv[0]); exit(1);
			fprintf(stderr, "\n\
Options:\n\
  -d FILE     dump (pre-)processed instance clauses to FILE\n\
  -D FILE     dump decision variables used into FILE\n\
  -h          display this help message\n\
  -r SEED     initialize random seed by SEED\n\
  -v          increase verbosity\n\
ksat written by Franz Brausse <brausse@informatik.uni-trier.de>, license: MIT\n");
		case 'r': srand(atoi(optarg)); break;
		case 'v': verbosity++; break;
		case '?':
			fprintf(stderr, "unknown option '-%c'\n", optopt);
			exit(1);
		case ':':
			fprintf(stderr, "missing parameter for option '-%c'\n",
			        optopt);
			exit(1);
		}

	if (argc - optind > 1) {
		fprintf(stderr, USAGE, argv[0]);
		exit(1);
	}

	FILE *in = stdin;
	if (argc - optind == 1 && !(in = fopen(argv[optind], "r"))) {
		perror(argv[optind]);
		exit(1);
	}
	int r = read_dimacs(solver, in);
	fclose(in);
	if (r < 0)
		exit(1);

	r = solver.run();
	if (verbosity > 0)
		solver.stats(verbosity);
	if (dump) {
		do_dump(solver, dump);
		fclose(dump);
	}
	switch (r) {
	case SAT: {
		printf("s SATISFIABLE\n");
		printf("v");
		unsigned n = 0;
		for (auto it = solver.units_begin(); it != solver.units_end(); ++it) {
			if (++n % 10 == 0)
				printf("\nv");
			printf(" %ld", lit_to_dimacs(it->implied_lit));
		}
		printf("\n");
		return 10;
	}
	case UNSAT:
		printf("s UNSATISFIABLE\n");
		return 20;
	}
	return r;
}
