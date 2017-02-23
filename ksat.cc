
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

void ksat::init(uint32_t nvars)
{
	this->nvars = nvars;
	vars    = new var_desc[nvars];
	watches = new vec<watch>[2*nvars];
	//assigns.init(nvars);
	units.reserve(nvars);
}

#include <sys/time.h>

struct timer {
	struct timeval tv;
	void start() { gettimeofday(&tv, NULL); }
	unsigned long get() const
	{
		struct timeval tw;
		gettimeofday(&tw, NULL);
		return (tw.tv_sec-tv.tv_sec)*1000000+(tw.tv_usec-tv.tv_usec);
	}
};

struct measurement {
	timer tt;
	unsigned long t = 0;
	unsigned long n = 0;

	void start() { tt.start(); }
	void stop() { t += tt.get(); }
	void tick() { n++; }
	double avg_us() const { return (double)t/n; }
};

const watch * ksat::propagate_units(unsigned long *propagations, unsigned long *pt)
{
	// fprintf(stderr, "%zu to be propagated, unsat: %u\n", units.size(), unsat);
	const watch *w = nullptr;
	unsigned long up = unit_ptr;
	timer t;
	t.start();
	for (; unit_ptr < units.size(); unit_ptr++) {
		w = propagate_single(units[unit_ptr].implied_lit);
		if (w)
			break;
	}
	unsigned long us = t.get();
	unsigned long n = (unit_ptr-up) + (w != nullptr);
	*propagations += n;
	*pt += us;
#if 0
	fprintf(stderr, "dl %zu: %ld[%u] propagations: %lu in %luus (%g props/sec)\n",
	        decisions.size(),
	        decisions.empty() ? 0 : lit_to_dimacs(units[decisions.back()].implied_lit),
	        decisions.empty() ? 0 : decisions.back(), n, t.get(), n/(us/1e6));
#endif
	return w;
}

lit ksat::next_decision() const
{
	for (uint32_t v=0; v<nvars; v++)
		if (!vars[v].have())
			return {2*v+!vars[v].value};
	return {2*nvars};
}

void ksat::trackback(uint32_t dlevel) // to including dlevel
{
	for (uint32_t i=dlevel; i<decisions.size(); i++)
		vars[var(units[decisions[i]].implied_lit)].value ^= 1;
	for (uint32_t i=decisions[dlevel]; i<units.size(); i++)
		vars[var(units[i].implied_lit)].trail_pos_plus1 = 0;
	units.resize(decisions[dlevel]);
	decisions.resize(dlevel);
	unit_ptr = units.size();
}

uint32_t ksat::resolve_conflict(std::vector<lit> &v, lit l, std::vector<lit> &cl, unsigned long *steps) const
{
	const watch *w = &units[vars[var(l)].trail_pos_plus1-1];
	assert(l == ~w->implied_lit);
	const lit *lqs, *lqe;
	lit clq[2];
	++*steps;
	deref(w->this_cl, clq, &lqs, &lqe);
#if 0
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

	assert(lqs[0] == ~l || lqs[1] == ~l);
	assert(v[0] == l || v[1] == l);

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
		return vars[var(a)].trail_pos_plus1 > vars[var(b)].trail_pos_plus1;
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
#if 0
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
		return resolve_conflict(v, ~units[most_recent_this_dl].implied_lit, cl, steps);
	}
}

template <typename V, typename Le>
void bin_heap_sift_up(V &v, uint32_t i, Le le)
{
	while (i && !le(v[i/2], v[i])) {
		swap(v[i/2], v[i]);
		i = i/2;
	}
}

template <typename V, typename Le>
void bin_heap_insert(V &v, lit l, Le le)
{
	uint32_t i = v.size();
	v.push_back(l);
	bin_heap_sift_up(v, i, le);
}

template <typename V, typename Le>
static void heapify(V &v, uint32_t i, const Le &le)
{
	while (1) {
		uint32_t c0 = 2*i+1;
		uint32_t min = i;
		if (c0 < v.size() && !le(v[min], v[c0]))
			min = c0;
		if (c0+1 < v.size() && !le(v[min], v[c0+1]))
			min = c0+1;
		if (min == i)
			return;
		swap(v[i], v[min]);
		i = min;
	}
}

template <typename V, typename Le>
static void build_bin_heap(V &v, const Le &le, uint32_t s=0)
{
	for (uint32_t i=v.size()/2; i>s; i--)
		heapify(v, i-1, le);
}

uint32_t ksat::analyze(const watch *w, vector<lit> (&v)[2], unsigned long *resolutions, unsigned long *rt) const
{
	uint32_t dec;
#if 1
	lit clp[2];
	const lit *a, *b;
	measurement m;
	m.start();
	deref(w->this_cl, clp, &a, &b);
#if 1
	auto tp1 = [this](lit l){ return vars[var(l)].trail_pos_plus1; };
	auto td = [tp1,k=decisions.back()](lit l){ return tp1(l) > k; };
	auto gt = [tp1](lit a, lit b){ return tp1(a) > tp1(b); };
	auto lit2tp = [tp1](lit l){ return lit{tp1(l) << 1 | sign(l)}; };
	auto tp2lit = [this](lit l){ return lit{var(units[var(l)-1].implied_lit)<<1 | sign(l)}; };
	lit l = w->implied_lit;
	v[0].clear();
	v[1].clear();
	v[1].reserve(b-a);
	for (; a < b; a++) {
		if (td(*a))
			v[1].push_back(lit2tp(*a));
		else
			v[0].push_back(*a);
	}
	while (v[1].size() > 1) {
#if 0
		fprintf(stderr, "resolve1:");
		for (int i=1; i>=0; i--)
			for (lit k : v[i])
				fprintf(stderr, " %ld[%u]", lit_to_dimacs(i ? tp2lit(k) : k), vars[var(i ? tp2lit(k) : k)].trail_pos_plus1-1);
		fprintf(stderr, "\n");
#endif
		unsigned max = 0;
		l = v[1][max];
		for (unsigned i=1; i<v[1].size(); i++) {
			lit k = v[1][i];
			if (l < k) {
				max = i;
				l = v[1][max];
			} else if (l == k) {
				v[1][i--] = v[1].back();
				v[1].pop_back();
			}
		}
		if (v[1].size() == 1)
			break;
		else if (v[1].size() > decisions.size()) {
			v[1].clear();
			goto out;
		}
		v[1][max] = v[1].back();
		v[1].pop_back();
		deref(units[var(l)-1].this_cl, clp, &a, &b);
#if 0
		fprintf(stderr, "dl %zu:%u resolve2:", decisions.size(), decisions.back());
		for (unsigned i=0; a+i<b; i++)
			fprintf(stderr, " %ld[%u]", lit_to_dimacs(a[i]), vars[var(a[i])].trail_pos_plus1-1);
		fprintf(stderr, "\n");
#endif
		v[1].push_back(lit2tp(lit2tp(a[0]) == ~l ? a[1] : a[0]));
		for (a += 2; a < b; a++)
			if (td(*a))
				v[1].push_back(lit2tp(*a));
			else
				v[0].push_back(*a);
#if 0
		fprintf(stderr, "resolved to");
		for (int i=1; i>=0; i--)
			for (lit k : v[i])
				fprintf(stderr, " %ld[%u]", lit_to_dimacs(i ? tp2lit(k) : k), vars[var(i ? tp2lit(k) : k)].trail_pos_plus1-1);
		fprintf(stderr, "\n");
#endif
		m.tick();
	}
	sort(v[0].begin(), v[0].end(), gt); /* lits according to tp1 descending */
	v[0].erase(unique(v[0].begin(), v[0].end()), v[0].end());
	assert(v[1].size() == 1);
	v[1].reserve(1+v[0].size());
	v[1][0] = tp2lit(v[1][0]);
	for (lit l : v[0])
		v[1].push_back(l);
	{
	uint32_t max_tp1 = v[0].empty() ? 0 : tp1(v[0][0]);
	for (dec=decisions.size(); dec>0; dec--)
		if (max_tp1 > decisions[dec-1])
			break;
	}
#if 0
	vector<lit> v(b-a-1+d-c-1);
	v[0] = a[0] == l ? a[1] : a[0];
	v[1] = c[0] == ~l ? c[1] : c[0];
	memcpy(v.data()+2, a+2, (b-a-2) * sizeof(lit));
	memcpy(v.data()+(b-a), c+2, (d-c-2) * sizeof(lit));
	auto heap = [this](lit p, lit c){
		return vars[var(p)].trail_pos_plus1 > vars[var(c)].trail_pos_plus1;
	};
	build_bin_heap(v, heap, 1);
	bool x;
	while ((x = tp(v[1]) > decisions.back()) ||
	       (v.size() > 2 && tp(v[2]) > decisions.back())) {
		/* at least 2 left on this decision level */
		l = v[0];
		deref(units[vars[var(l)].trail_pos_plus1-1].this_cl, clq, &c, &d);
		v[0] = c[0] == ~l ? c[1] : c[0];
		
	}
	dec = resolve_conflict2(v, l, cl, &m.n);
#endif
#else
	vector<lit> v(a, b);
	dec = resolve_conflict(v, w->implied_lit, cl, &m.n);
#endif
	m.stop();
	*resolutions += m.n;
	*rt += m.t;
#if 0
	fprintf(stderr, "dl %zu:%u resolution done in %luus, %lu steps, resulted in clause of size %zu on dl %u\n",
	        decisions.size(), decisions.back(), m.t, m.n, v[1].size(), dec);
#endif
#else
	cl.clear();
#endif
	if (0 && v[1].empty()) { // cl.size() > decisions.size() || !vars[var(cl[most_recent_this_dl])].have()
out:
		v[1].resize(decisions.size());
		for (uint32_t i=0; i<decisions.size(); i++)
			v[1][decisions.size()-1-i] = ~units[decisions[i]].implied_lit;
		return decisions.size()-1;
	} else {
		return dec;
	}
}

int ksat::run()
{
	vector<lit> cl[2];
	unsigned long conflicts = 0, n_decisions = 0, propagations = 0, resolutions = 0;
	unsigned long pt = 0, rt = 0;
	timer t;
	t.start();
	int r = 0;
	uint32_t learnt_lits = 0;
	unsigned long last_out = 0;
	while (1) {
		while (const watch *w = propagate_units(&propagations, &pt)) {
			++conflicts;
			if (t.get()-last_out > 1000000) {
				last_out = t.get();
				uint32_t n = 0;
				for (const auto &c : db.chunks)
					n += c.valid;
				double s = t.get()/1e6;
				fprintf(stderr, "time: %.1fs, conflicts: %lu (%.1f/s), avg. learnt sz: %.1f lits, decisions: %lu (%.1f/s), propagations: %lu (%.4g/s), resolutions: %lu (%.4g/s), cl db: %u MiB\n",
					s,
					conflicts, conflicts/s,
					10*learnt_lits/conflicts*.1,
					n_decisions, n_decisions/s,
					propagations, propagations/(pt/1e6),
					resolutions, resolutions/(rt/1e6),
					n>>(20-2));
			}
			if (decisions.empty()) {
				unsat = true;
				r = 20;
				goto done;
			}
			uint32_t decision_level = analyze(w, cl, &resolutions, &rt);
			learnt_lits += cl[1].size();
			trackback(decision_level);
			add_clause0(cl[1]);
		}
		lit d = next_decision();
		if (var(d) >= nvars) {
			r = 10;
			goto done;
		}
		n_decisions++;
		// fprintf(stderr, "dl %zu: next decision %ld[%zu]\n", decisions.size(), lit_to_dimacs(d), units.size());
		decisions.push_back(units.size());
		units.push_back({clause_proxy{.ptr = CLAUSE_PTR_NULL},d});
		vars[var(d)] = var_desc{sign(d),(uint32_t)units.size()};
	}
done:
	fprintf(stderr, "time: %luus, conflicts: %lu, decisions: %lu, propagations: %lu, resolutions: %lu\n",
	        t.get(), conflicts, n_decisions, propagations, resolutions);
	return r;
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

void ksat::add_clause0(vector<lit> &cl)
{
	unsigned j=0;
#if 0
	fprintf(stderr, "adding clause");
	unsigned i;
	for (i=0; i<std::min((uint32_t)cl.size(), 5U); i++)
		fprintf(stderr, " %ld[%d]", lit_to_dimacs(cl[i]), vars[var(cl[i])].trail_pos_plus1-1);
	if (i < cl.size())
		fprintf(stderr, " ...");
	fprintf(stderr, "\n");
#endif
#if 0
	for (unsigned i=0; j<2 && i<cl.size(); i++)
		if (!vars[var(cl[i])].have()) {
			assert(j == i);
			swap(cl[j++], cl[i]);
		} else
			assert(vars[var(cl[i])].value != sign(cl[i]));
#else
	j = 1;
#endif
	if (cl.size() < 2) {
		assert(decisions.empty());
		if (cl.size() == 0 || !add_unit(cl[0]))
			unsat = true;
		return;
	}
	assert(j == 1);
	clause_proxy p;
	/* 0 and especially 1 must be those assigned latest!!! */
#if 0
	unsigned w = 1;
	for (unsigned k=2; k<cl.size(); k++)
		if (vars[var(cl[k])].trail_pos_plus1 >
		    vars[var(cl[w])].trail_pos_plus1) {
			assert(0);
			w = k;
		}
	swap(cl[1], cl[w]);
#endif
	if (cl.size() == 2) {
		p.l[0] = cl[0] | CLAUSE_PROXY_BIN_MASK;
		p.l[1] = cl[1] | CLAUSE_PROXY_BIN_MASK;
	} else {
		p.ptr = db.add(cl.size(), true);
		memcpy(db[p.ptr].l, cl.data(), sizeof(lit)*cl.size());
	}
	watches[cl[0]].push_back({p,cl[1]});
	watches[cl[1]].push_back({p,cl[0]});
	if (j == 1 && cl.size() > 1) {
		bool ok = add_unit(cl[0], p);
		assert(ok);
	}
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
