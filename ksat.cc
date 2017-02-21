
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

lit ksat::next_decision()
{
	for (uint32_t v=0; v<nvars; v++)
		if (!vars[v].have())
			return {2*v+!vars[v].value};
	return {2*nvars};
}

void ksat::trackback(uint32_t dlevel) // to including dlevel
{
	for (uint32_t i=decisions[dlevel]; i<units.size(); i++)
		vars[var(units[i].implied_lit)].trail_pos_plus1 = 0;
	units.resize(decisions[dlevel]);
	decisions.resize(dlevel);
	unit_ptr = units.size();
}

uint32_t ksat::resolve_conflict(std::vector<lit> &v, lit l, std::vector<lit> &cl)
{
	const watch *w = &units[vars[var(l)].trail_pos_plus1-1];
	assert(l == ~w->implied_lit);
	const lit *lqs, *lqe;
	lit clq[2];
	deref(w->this_cl, clq, &lqs, &lqe);
#if 1
	fprintf(stderr, "resolve1:");
	for (lit k : v)
		fprintf(stderr, " %ld[%u]", lit_to_dimacs(k), vars[var(k)].trail_pos_plus1-1);
	fprintf(stderr, "\n");
	fprintf(stderr, "resolve2:");
	for (unsigned i=0; lqs+i<lqe; i++)
		fprintf(stderr, " %ld[%u]", lit_to_dimacs(lqs[i]), vars[var(lqs[i])].trail_pos_plus1-1);
	fprintf(stderr, "\n");
#endif
	assert(!v.empty());
	assert(lqs < lqe);
	unsigned m = lqe-lqs-1 + v.size()-1;
	cl.resize(lqe-lqs-1 + v.size()-1);
	unsigned j=0;
	for (lit k : v)
		if (k != l)
			cl[j++] = k;
	for (; lqs < lqe; lqs++)
		if (*lqs != ~l)
			cl[j++] = *lqs;
	// cl.resize(j);
	assert(m == j);
	sort(cl.begin(), cl.begin()+m, [this](lit a, lit b){
		return vars[var(a)].trail_pos_plus1 < vars[var(b)].trail_pos_plus1;
	});
	assert(m > 0);
	unsigned n_this_dl = 0;
	uint32_t max_tp = 0;
	uint32_t most_recent_this_dl = 0;
	j = cl.size() != 0;
	for (unsigned i=0; i<m; i++) {
		lit k = cl[i];
		if (i > 0) {
			uint32_t x = cl[j-1] ^ k;
			if (!x) continue;
			if (x == 1) {
				fprintf(stderr, "tautology\n");
				cl.clear();
				return decisions.size()-1;
			}
			cl[j++] = k;
		}
		uint32_t tp = vars[var(k)].trail_pos_plus1-1;
		if (tp >= decisions.back()) {
			if (!n_this_dl++ || most_recent_this_dl < tp)
				most_recent_this_dl = tp;
		} else if (max_tp < tp)
			max_tp = tp;
	}
	cl.resize(j);
#if 1
	fprintf(stderr, "resolved to");
	for (lit k : cl)
		fprintf(stderr, " %ld[%u]", lit_to_dimacs(k), vars[var(k)].trail_pos_plus1-1);
	fprintf(stderr, "\n");
	fprintf(stderr, "dl: %zu[%u], on this dl: %u, max_tp not on this dl: %u, most recent on this dl: %u, j: %u\n",
	        decisions.size()-1, decisions.back(), n_this_dl, max_tp, most_recent_this_dl, j);
#endif
	if (n_this_dl <= 1) {
		unsigned dec;
		for (dec=decisions.size(); dec>0; dec--)
			if (max_tp >= decisions[dec-1])
				break;
		return dec;
	} else {
		// resolve cl with the reason for the most recently implied (false) literal in cl
		swap(v, cl);
		return resolve_conflict(v, ~units[most_recent_this_dl].implied_lit, cl);
	}
}

uint32_t ksat::analyze(const watch *w, vector<lit> &cl)
{
	lit clp[2];
	const lit *a, *b;
	deref(w->this_cl, clp, &a, &b);
	vector<lit> v(a, b);
	uint32_t dec = resolve_conflict(v, w->implied_lit, cl);
	fprintf(stderr, "resolution done, resulted in clause of size %zu\n", cl.size());

	if (cl.empty()) { // cl.size() > decisions.size() || !vars[var(cl[most_recent_this_dl])].have()
		for (uint32_t i : decisions)
			cl.push_back(~units[i].implied_lit);
		return decisions.size()-1;
	} else {
		return dec;
	}
}

void ksat::add_clause0(vector<lit> &cl)
{
	clause_proxy p;
	unsigned j=0;
	bool sat = false;
	for (unsigned i=0; j<2 && i<cl.size(); i++)
		if (!vars[var(cl[i])].have())
			swap(cl[j++], cl[i]);
		else
			sat |= vars[var(cl[i])].value == sign(cl[i]);
	assert(j <= 1);
	assert(!sat);
	assert(cl.size() >= 2);
	/* 0 and especially 1 must be those assigned latest!!! */
	unsigned w = 1;
	for (unsigned k=2; k<cl.size(); k++)
		if (vars[var(cl[k])].trail_pos_plus1 >
		    vars[var(cl[w])].trail_pos_plus1)
			w = k;
	swap(cl[1], cl[w]);
	switch (cl.size()) {
	case 1:
		if (add_unit(cl[0]))
			return;
		/* fall through */
	case 0:
		unsat = true;
		return;
	case 2:
		p.l[0] = cl[0] | CLAUSE_PROXY_BIN_MASK;
		p.l[1] = cl[1] | CLAUSE_PROXY_BIN_MASK;
		break;
	default:
		p.ptr = db.add(cl.size(), true);
		if (p.ptr.offset == 145188) {
			//abort();
		}
		memcpy(db[p.ptr].l, cl.data(), sizeof(lit)*cl.size());
		break;
	}
	watches[cl[0]].push_back({p,cl[1]});
	watches[cl[1]].push_back({p,cl[0]});
	if (j == 1 && cl.size() > 1) {
		bool ok = add_unit(cl[0], p);
		assert(ok);
	}
}

int ksat::run()
{
	vector<lit> cl;
	while (1) {
		while (const watch *w = propagate_units()) {
			if (decisions.empty()) {
				unsat = true;
				return 20;
			}
			uint32_t decision_level = analyze(w, cl);
			trackback(decision_level);
			add_clause0(cl);
		}
		lit d = next_decision();
		if (var(d) >= nvars)
			return 10;
		decisions.push_back(units.size());
		units.push_back({clause_proxy{.ptr = CLAUSE_PTR_NULL},d});
		vars[var(d)] = var_desc{sign(d),(uint32_t)units.size()};
	}
	return 0;




	unsat |= (bool)propagate_units();

	for (lit d; !unsat && var(d = next_decision()) < nvars;) {
		decisions.push_back(units.size());
		units.push_back({clause_proxy{.ptr = CLAUSE_PTR_NULL},d});
		vars[var(d)] = var_desc{sign(d),(uint32_t)units.size()};
		const watch *w;
		while (unit_ptr < units.size() && (w = propagate_units())) {
			if (!decisions.size()) {
				unsat = true;
				break;
			}
			uint32_t decision_level = analyze(w, cl);
			trackback(decision_level);
			add_clause0(cl);
			cl.clear();
		}
	}
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
	vec<watch> &wnl = watches[~l];
	for (unsigned i=0; i<wnl.size(); i++) {
		watch &w = wnl[i];
		lit implied = w.implied_lit;
		var_desc &v_implied = vars[var(implied)];
		if (v_implied.have() && v_implied.value == sign(implied))
			continue;
		if (is_ptr(w.this_cl)) {
			clause_ptr cl_ptr = w.this_cl.ptr;
			clause &c = db[cl_ptr];
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
				c.l[j] = ~l;
				c.l[widx] = k;

				i--;

				for (watch &v : watches[implied])
					if (cl_ptr == v.this_cl.ptr) {
						assert(v.implied_lit == ~l);
						v.implied_lit = k;
						break;
					}

				goto done;
			}
		}
		if (v_implied.have())
			return &w;
		units.emplace_back(w);
		v_implied = var_desc{sign(implied),(uint32_t)units.size()};
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

bool ksat::add_unit(lit l, const clause_proxy &p)
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
	units.push_back({p,l});
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
	c.resize(n);
	unsigned j=0;
	bool sat = false;
	for (unsigned i=0; !sat && j<2 && i<c.size(); i++)
		if (!vars[var(c[i])].have())
			swap(c[j++], c[i]);
		else
			sat |= vars[var(c[i])].value == sign(c[i]);
	if (c.size() >= 2) {
		clause_proxy p;
		if (c.size() == 2) {
			p.l[0] = c[0] | CLAUSE_PROXY_BIN_MASK;
			p.l[1] = c[1] | CLAUSE_PROXY_BIN_MASK;
		} else {
#if 0
			unsigned w1 = rand() % n;
			unsigned w2 = rand() % (n-1);
			if (w2 >= w1)
				w2++;
			if (w1 > w2)
				swap(w1, w2);
			swap(c[0], c[w1]);
			swap(c[1], c[w2]);
#endif
			p.ptr = db.add(n, false);
			memcpy(db[p.ptr].l, c.data(), n*sizeof(lit));
		}
		watches[c[0]].push_back({p, c[1]});
		watches[c[1]].push_back({p, c[0]});
	}
	if (!sat)
		switch (j) {
		case 1:
			if (add_unit(c[0]))
				return;
			/* fall through */
		case 0:
			unsat = true;
			return;
		}
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
