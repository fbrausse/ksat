
#include <cassert>
#include <algorithm>	/* std::sort */
#include <cstring>	/* memcpy() */
#include <cstdio>	/* FILE, fprintf() */

#include "ksat.hh"

using std::swap;
using std::vector;
using std::forward_list;

#define CHUNK_SIZE	(uint32_t)((1U << 26 /* 64 MiB */) / sizeof(uint32_t))

clause_db::chunk::chunk(uint32_t sz)
: size(sz), valid(0), v(new uint32_t[sz])
{}

clause_db::chunk::chunk(chunk &&o)
: size(o.size), valid(o.valid), v(o.v)
{ o.v = nullptr; }

clause_db::chunk::~chunk()
{
	delete[] v;
}

clause & clause_db::chunk::operator[](uint32_t off) const
{
	return *reinterpret_cast<clause *>(v + off);
}

clause_ptr clause_db::alloc(uint32_t size)
{
	/* TODO: optimize search */
	uint32_t idx;
	for (idx=0; idx<chunks.size(); idx++)
		if (chunks[idx].size - chunks[idx].valid >= size)
			break;
	if (idx == chunks.size())
		chunks.emplace_back(std::max(size, CHUNK_SIZE));
	chunk &ch = chunks[idx];
	clause_ptr r = { idx, ch.valid };
	ch.valid += size;
	return r;
}

clause & clause_db::operator[](clause_ptr p) const
{
	return chunks[p.chunk_idx][p.offset];
}

clause_ptr clause_db::add(uint32_t size, bool learnt)
{
	clause_ptr ptr = alloc(size+1);
	struct clause &cl = (*this)[ptr];
	cl.header.size = size;
	cl.header.learnt = learnt;
	return ptr;
}

clause_db::clause_db()
{
	add(0, false); /* reserve {0,0} clause_ptr (equiv null) */
}

ksat::~ksat()
{
	delete[] vars;
	delete[] watches;
}

#include <sys/time.h>

const watch * ksat::propagate_units(void)
{
	fprintf(stderr, "%zu to be propagated, unsat: %u\n", units.size(), unsat);
	unsigned props = 0;
	struct timeval tv, tw;
	gettimeofday(&tv, NULL);
	const watch *w = nullptr;
	//bool p = false;
	for (; unit_ptr < units.size(); unit_ptr++) {
		w = propagate_single(units[unit_ptr].implied_lit);
#if 0
		fprintf(stderr, "propagation of %ld: %s\n",
		        lit_to_dimacs(units[unit_ptr]), p ? "conflict" : "OK");
#endif
		props++;
		if (w)
			break;
	}
	gettimeofday(&tw, NULL);
	long us = (tw.tv_sec-tv.tv_sec)*(long)1e6+(tw.tv_usec-tv.tv_usec);
	fprintf(stderr, "propagations: %u in %luus (%g props/sec)\n",
	        props, us, props/(us/1e6));
	return w;
}

int ksat::run()
{
	unsat |= (bool)propagate_units();
	return 0;
}

void ksat::init(uint32_t nvars)
{
	this->nvars = nvars;
	vars    = new var_desc[nvars];
	watches = new vec<watch>[2*nvars];
	//assigns.init(nvars);
	units.reserve(nvars);
}

const watch * ksat::propagate_single(lit l)
{
//	fprintf(stderr, "propagating %ld\n", lit_to_dimacs(l));
	vec<watch> &wnl = watches[~l];
	for (unsigned i=0; i<wnl.size(); i++) {
		watch &w = wnl[i];
		lit implied = w.implied_lit;
		// assignments::lptr a_implied = assigns[w.implied_lit];
		var_desc &v_implied = vars[var(implied)];
		if (v_implied.have() && v_implied.value == sign(implied))
			continue;
		if (is_ptr(w.this_cl)) {
			clause_ptr cl_ptr = w.this_cl.ptr;
			clause &c = db[cl_ptr];
		#if 1
			unsigned j_true = 0, j_undef = 0;
			for (unsigned j=2; j<c.header.size && !j_true; j++) {
				lit k = c.l[j];
				const var_desc &vk = vars[var(k)];
				if (vk.have()) {
					if (vk.value == sign(k))
						j_true = j;
				} else //if (!j_undef)
					j_undef = j; // take last undef'ed lit
			}
			if (j_true || j_undef) {
				unsigned j = j_true ? j_true : j_undef;
				lit k = c.l[j];

				watches[k].push_back(w);
				w = wnl.back();
				wnl.pop_back();

				unsigned widx = c.l[1] == ~l;
				assert(c.l[widx] == ~l);
				// swap(c.l[j], c.l[widx]);
				c.l[j] = ~l;
				c.l[widx] = k;

				i--;

				for (watch &v : watches[implied])
					if (cl_ptr == v.this_cl.ptr) {
						// fprintf(stderr, " (impl:%ld)", lit_to_dimacs(v.implied_lit));
						assert(v.implied_lit == ~l);
						v.implied_lit = k;
						break;
					}

				goto done;
			}
		#else
			for (unsigned j=2; j<c.header.size; j++) {
				lit k = c.l[j];
				//assignments::lptr a_k = assigns[k];
				/* a_k.same() => k != w.implied_lit && k != ~l */
				//if (!(vars[var(k)].implied & (1 << sign(~k)))/*!a_k.other()*/)
				if (!vars[var(k)].have() || vars[var(k)].value == sign(k))
				{
					/* switch watch from ~l to k */
				#if 0
					fprintf(stderr, "switching watch (cl: %u:%u impl:%ld) %ld -> %ld",
						w.this_cl.chunk_idx, w.this_cl.offset,
						lit_to_dimacs(w.implied_lit), lit_to_dimacs(~l), lit_to_dimacs(k));
				#endif
					watches[k].push_back(w);
					w = wnl.back();
					wnl.pop_back();
				#if 1
					unsigned widx = c.l[1] == ~l;
					assert(c.l[widx] == ~l);
					// swap(c.l[j], c.l[widx]);
					c.l[j] = ~l;
					c.l[widx] = k;
				#endif
					i--;
				#if 1
					for (watch &v : watches[implied])
						if (cl_ptr == v.this_cl.ptr) {
							// fprintf(stderr, " (impl:%ld)", lit_to_dimacs(v.implied_lit));
							assert(v.implied_lit == ~l);
							v.implied_lit = k;
							break;
						}
				#endif
					//fprintf(stderr, "\n");
					goto done;
				}
			}
		#endif
		}
#if 0
		fprintf(stderr, " -> implied %ld, assign have:%d\n",
		        lit_to_dimacs(w.implied_lit), a_implied.have());
#endif
		if (v_implied.have())
			return &w;
		// fprintf(stderr, " -> enqueuing implied %ld\n", lit_to_dimacs(w.implied_lit));
		units.emplace_back(w);
		v_implied = var_desc{sign(implied),(uint32_t)units.size()};
	//	a_implied.set();
	//	vars[var(w.implied_lit)].trail_pos_plus1 = units.size();
	//	vars[var(w.implied_lit)].cause++;
	//	vars[var(w.implied_lit)].reason = w.this_cl;
	done:;
	/*
		if (clause satisfied through w2)
			continue;
		else if (exists k assigned true in clause)
			switch w1 to k
		else if (exists k unassigned and unwatched in clause)
			switch watch from ~l to k
		else if (exists k unassigned in clause)
			switch w1 to k (k is the other watched lit)
			enqueue unit k
		else
			conflict clause
	*/
	}
	return nullptr;
}

bool ksat::add_unit(lit l)
{
#if 0
	auto a = assigns[l];
	// if (a & (1 << sign(l)))
	if (a.same())
		return true;
	// if ((a |= 1 << sign(l)) == 3)
	if (a.other())
		return false;
	a.set();
#else
	auto &v = vars[var(l)];
	if (v.have() && v.value == sign(l))
		return true;
	if (v.have())
		return false;
#endif
	units.push_back({clause_proxy{.ptr=CLAUSE_PTR_NULL},l});
	v = var_desc{sign(l),(uint32_t)units.size()};
	return true;
}

void ksat::add_clause(vector<lit> &c)
{
	sort(c.begin(), c.end());
	unsigned n = c.size() != 0;
	for (unsigned i=n; i<c.size(); i++) {
		uint32_t k = c[n-1] ^ c[i];
		if (!k)
			continue; /* remove duplicate literal */
		if (k == 1)
			return; /* dismiss clause, always satisfied */
		c[n++] = c[i];
	}
	clause_proxy p;
	unsigned w1 = 0;
	unsigned w2 = 1;
	switch (n) {
	case 1:
		if (add_unit(c[0]))
			return;
		/* fall through */
	case 0:
		fprintf(stderr, "init unsat (n: %u):", n);
		for (lit l : c)
			fprintf(stderr, " %ld", lit_to_dimacs(l));
		fprintf(stderr, "\n");
		unsat = true;
		return;
	case 2:
		p.l[0] = c[0] | CLAUSE_PROXY_BIN_MASK;
		p.l[1] = c[1] | CLAUSE_PROXY_BIN_MASK;
		break;
	default:
#if 0
		w1 = rand() % n;
		w2 = rand() % (n-1);
		if (w2 >= w1)
			w2++;
		{
			if (w1 > w2)
				swap(w1, w2);
			swap(c[0], c[w1]);
			swap(c[1], c[w2]);
			w1 = 0;
			w2 = 1;
		}
#endif
		p.ptr = db.add(n, false);
		memcpy(db[p.ptr].l, c.data(), n*sizeof(lit));
		break;
	}
	watches[c[w1]].push_back({p, c[w2]});
	watches[c[w2]].push_back({p, c[w1]});
}

void ksat::stats(int verbosity)
{
	fprintf(stderr, "vars: %lu MiB\n",
	        (sizeof(*vars) * nvars) >> 20);
#if 0
	if (verbosity > 1) {
		std::vector<uint32_t> vcause;
		unsigned long total = 0;
		for (uint32_t v=0; v<nvars; v++) {
			vcause.resize(std::max((uint32_t)vcause.size(), vars[v].cause+1));
			vcause[vars[v].cause]++;
		}
		for (uint32_t i=0; i<vcause.size(); i++) {
			total += i*vcause[i];
			if (vcause[i])
				fprintf(stderr, "\t#causing %u: %u\n", i, vcause[i]);
		}
		fprintf(stderr, "\ttotal: %lu\n", total);
	}
#endif
	fprintf(stderr, "watches (each cached: %u): %lu MiB\n",
	        watches[0].init_cap(), (sizeof(*watches) * nvars*2) >> 20);
	if (verbosity > 1) {
		std::vector<size_t> wfilled;
		for (uint32_t v=0; v<2*nvars; v++) {
			size_t sz = watches[v].size();
			wfilled.resize(std::max(wfilled.size(), sz+1));
			wfilled[sz]++;
		}
		for (uint32_t i=0; i<wfilled.size(); i++)
			if (wfilled[i])
				fprintf(stderr, "\tlen %u: %zu\n", i, wfilled[i]);
	}
	fprintf(stderr, "units: %lu MiB\n",
	        (sizeof(lit) * units.capacity()) >> 20);
	fprintf(stderr, "%u chunks (cached: %u):", db.chunks.size(), db.chunks.init_cap());
	for (const clause_db::chunk &ch : db.chunks)
		fprintf(stderr, " %u:%u (%lu MiB)",
		        ch.valid, ch.size, (ch.size * sizeof(*ch.v)) >> 20);
	fprintf(stderr, "\n");
	size_t n_bin = 0, n_lg = 0;
	std::vector<uint32_t> lg_sz;
	for (auto it = binary_clauses_begin(); it != binary_clauses_end(); ++it)
		n_bin++;
	for (auto it = large_clauses_begin(); it != large_clauses_end(); ++it) {
		lg_sz.resize(std::max((uint32_t)lg_sz.size(), it->header.size+1U));
		lg_sz[it->header.size]++;
		n_lg++;
	}
	fprintf(stderr, "%u vars; %zu binary, %zu large clauses:\n", nvars, n_bin, n_lg);
	if (verbosity > 1)
		for (uint32_t i=0; i<lg_sz.size(); i++)
			if (lg_sz[i])
				fprintf(stderr, "\t%u: %u\n", i, lg_sz[i]);
	fprintf(stderr, "%zu units to be propagated, unsat: %d\n", units.size(), unsat);
}
