
#include <cassert>
#include <algorithm>	/* std::sort */
#include <cstring>	/* memcpy() */
#include <cstdio>	/* FILE, fprintf() */

#include "ksat.hh"

/* TODO [.: weak dep; !: dep; ?: related]:
 * a) learnt clause minimization [Sörensson/Biere'09]
 *   a1) local: self-subsuming resolution
 *   a2) global
 * b) intro special watch lists/handling for binary clauses
 * c.a) compute/update LBD:
 *   c1) keep LBD=2 clauses
 *   c2) prune large-LBD clauses
 * d!c) restart if learnt clause quality (via LBD) is low over a longer period
 * e?c2) use SLUB-like allocator for clause_db
 */

using std::swap;
using std::vector;
using std::forward_list;

namespace ksat_ns {

#define CHUNK_SIZE	(uint32_t)((1U << 26 /* 64 MiB */) / sizeof(uint32_t))

clause_db::chunk::chunk(uint32_t sz)
: size(sz), valid(0), v(new uint32_t[sz])
{}

clause_db::chunk::chunk(chunk &&o)
: size(o.size), valid(o.valid), v(o.v)
{ o.v = nullptr; }

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
	cl.header.remove = 0;
	return ptr;
}

clause_db::clause_db()
{
	add(0, false); /* reserve {0,0} clause_ptr (equiv null) */
}

struct statistics {
	unsigned long conflicts = 0, n_decisions = 0, propagations = 0, resolutions = 0, learnt = 0;
	unsigned long pt = 0, rt = 0, dt = 0, tt = 0, wft = 0;
	unsigned long learnt_lits = 0;
	unsigned long last_out = 0;
	unsigned long restarts = 0;
	timer t;
	const ksat &sat;
	statistics(const ksat &sat) : sat(sat) { t.start(); }

	void operator()()
	{
		last_out = t.get();
		uint32_t n = 0;
		for (const auto &c : sat.db.chunks)
			n += c.valid;
		double s = t.get()/1e6;
		uint32_t fixed = sat.decisions.empty() ? sat.units.size() : sat.decisions.front();
		fprintf(stderr,
		        "time: %.1fs, vars: %u+%u, confl: %lu (%.1f/s), rst: %lu, learnt: %lu avg. lits: %.1f, "
		        "decs: %lu (%.1f/s) %.1fs, dl: %zu, props: %lu (%.4g/s) %.1fs %.1fs, res: %lu (%.4g/s) %.1fs, tt: %.1fs, cl db: %u MiB\n",
		        s, fixed, sat.nvars-fixed,
		        conflicts, conflicts/s, restarts,
		        learnt, 10*learnt_lits/(conflicts+1)*.1,
		        n_decisions, n_decisions/s, dt/1e6, sat.decisions.size(),
		        propagations, propagations/(pt/1e6), pt/1e6, wft/1e6,
		        resolutions, resolutions/(rt/1e6), rt/1e6,
		        tt/1e6,
		        n>>(20-2));
	}
};

struct bin_inv_heap {

	const uint32_t *keys;
	uint32_t *paeh; /* mapping var -> heap index */
	uint32_t *heap; /* mapping heap index -> var */
	uint32_t n, valid;

	explicit bin_inv_heap(const uint32_t *keys, uint32_t n)
	: keys(keys), paeh(new uint32_t[n]), heap(new uint32_t[n]), n(n), valid(n)
	{
		for (uint32_t i=0; i<n; i++)
			heap[i] = paeh[i] = i;
	}

	~bin_inv_heap()
	{
		delete[] paeh;
		delete[] heap;
	}

	void swap(uint32_t &va, uint32_t &vb)
	{
		std::swap(paeh[va], paeh[vb]);
		std::swap(va, vb);
	}

	uint32_t pop()
	{
		uint32_t r = heap[0];
		swap(heap[0], heap[--valid]);
		sift_down(0);
		return r;
	}

	bool le(uint32_t a, uint32_t b) const
	{
		return keys[a] > keys[b];
	}

	void sift_down(uint32_t i)
	{
		while (true) {
			uint32_t c = i;
			if (2*i+1 < valid && !le(heap[c], heap[2*i+1]))
				c = 2*i+1;
			if (2*i+2 < valid && !le(heap[c], heap[2*i+2]))
				c = 2*i+2;
			if (i == c)
				break;
			swap(heap[i], heap[c]);
			i = c;
		}
	}

	void sift_up(uint32_t i)
	{
		while (i && !le(heap[i/2], heap[i])) {
			swap(heap[i/2], heap[i]);
			i = i/2;
		}
	}

	void build()
	{
		for (uint32_t i=valid/2; i; i--)
			sift_down(i-1);
	}

	uint32_t idx(uint32_t v) const { return paeh[v]; }

	void restore(uint32_t nvalid)
	{
		assert(nvalid >= valid);
		valid = nvalid;
		build();
	}
};

void ksat::bin_cl_itr::skip_non_bin()
{
	for (; pos() < 2*sat.nvars; ++pos(), pos_idx=0) {
		const auto &ww = sat.watches[pos()];
		for (; pos_idx < ww.size(); pos_idx++) {
			const watch &w = ww[pos_idx];
			if (!is_ptr(w.this_cl) && pos() < w.implied_lit) {
				tmp_cl[2] = w.implied_lit;
				return;
			}
		}
	}
}

ksat::bin_cl_itr & ksat::bin_cl_itr::operator++()
{
	++pos_idx;
	skip_non_bin();
	return *this;
}

ksat::clause_itr ksat::cl_ref::begin() const
{
	return {
		sat.binary_clauses_begin(),
		sat.binary_clauses_end(),
		sat.large_clauses_begin()
	};
}

ksat::clause_itr ksat::cl_ref::end() const
{
	return {
		sat.binary_clauses_end(),
		sat.binary_clauses_end(),
		sat.large_clauses_end()
	};
}

ksat::~ksat()
{
	delete lit_heap;
	delete[] vsids;
	delete[] watches;
	delete[] vars;
}

void ksat::init(uint32_t nvars)
{
	this->nvars = nvars;
	vars    = new var_desc[nvars];
	watches = new vec<watch>[2*nvars];
	//assigns.init(nvars);
	units.reserve(nvars);
	vsids = new uint32_t[2*nvars];
	memset(vsids, 0, sizeof(*vsids)*2*nvars);
	//lit_heap = new bin_inv_heap(vsids, 2*nvars);
#if 1
	active = new uint32_t[nvars];
	for (uint32_t v=0; v<nvars; v++)
		active[v] = v;
	n_active = nvars;
#endif
}

void ksat::vacuum()
{
	assert(decisions.empty());
	uint32_t n = decisions.empty() ? units.size() : decisions.front();
	measurement m;
	m.start();
	uint32_t del_w = 0, del_db = 0;
#if 1
	clause_db ndb;
	for (uint32_t i=0; i<2*nvars; i++) {
		vec<watch> &ww = watches[i];
		for (uint32_t j=0; j<ww.size(); j++) {
			m.tick();
			watch &w = ww[j];
			clause *c = nullptr;
			lit tmp[2];
			lit *a, *b;
			if (is_ptr(w.this_cl))
				c = &db[w.this_cl.ptr];
			if (is_ptr(w.this_cl) && db[w.this_cl.ptr].header.remove) {
				memcpy((void *)&w.this_cl, c->l, sizeof(w.this_cl));
				c = nullptr;
				ndb.deref(w.this_cl, tmp, &a, &b);
			} else {
				db.deref(w.this_cl, tmp, &a, &b);
				uint32_t open = 0;
				bool sat = false;
				for (uint32_t k=0; !sat && a+k<b; k++) {
				#if 1
					status r = value(a[k]);
					if (!valid(r))
						a[open++] = a[k];
					else
						sat = r&1;
				#else
					const var_desc &vk = vars[var(a[k])];
					if (!vk.have())
						a[open++] = a[k];
					else if (assert(vk.trail_pos_plus1 <= n), vk.value == sign(a[k]))
						sat = true;
					//else
					//	a[open++] = a[k];
				#endif
				}
				assert(sat || open >= 2);
				if (sat) {
					w = ww.back();
					ww.pop_back();
					j--;
					del_db += b-a > 2 ? (b-a)+1 : 0;
					del_w++;
					continue;
				} else if (open == 2) {
					w.this_cl.l[0] = a[0] | CLAUSE_PROXY_BIN_MASK;
					w.this_cl.l[1] = a[1] | CLAUSE_PROXY_BIN_MASK;
				} else {
					w.this_cl.ptr = ndb.add(open, db[w.this_cl.ptr].header.learnt);
					memcpy(ndb[w.this_cl.ptr].l, a, open*sizeof(lit));
				}
			}
			assert(a[0] == i || a[1] == i);
			if (have(w.implied_lit)) {
				w.implied_lit = a[0] == i ? a[1] : a[0];
				//watches[w.implied_lit].push_back({w.implied_lit < i ? w.this_cl : save,i});
				assert(!have(w.implied_lit));
			}
			if (c) {
				del_db += is_ptr(w.this_cl) ? c->header.size - ndb[w.this_cl.ptr].header.size : (c->header.size+1);
				c->header.remove = 1;
				memcpy(c->l, (void *)&w.this_cl, sizeof(w.this_cl));
			}
		}
	}
	db.~clause_db();
	new (&db) clause_db(std::move(ndb));
#endif
	for (uint32_t v=0; v<n_active; v++) {
		uint32_t w = active[v];
		if (have(w) && vars[w].trail_pos() < n)
			active[v--] = active[--n_active];
	}
	m.stop();
	fprintf(stderr, "vacuum del %u watches, %u large-cl lits (%lu steps in %luus -> %g/s)\n", del_w, del_db, m.n, m.t, m.n/(m.t/1e6));
}

void ksat::reg(lit a) const
{
	if (!++vsids[a]) {
		dec_all();
		vsids[a] = 1U << 31;
	}
//	if (lit_heap)
//		lit_heap->sift_up(lit_heap->idx(a));
}

void ksat::dec_all() const
{
	for (uint32_t i=0; i<2*nvars; i++)
		vsids[i] = (vsids[i]+1)>>1;
}

const watch * ksat::propagate_units(struct statistics *stats)
{
	// fprintf(stderr, "%zu to be propagated, unsat: %u\n", units.size(), unsat);
	const watch *rw = nullptr;
	unsigned long up = unit_ptr;
	timer t;
	t.start();
	for (; unit_ptr < units.size(); unit_ptr++) {
		lit l = units[unit_ptr].implied_lit;
		vec<watch> &wnl = watches[~l];
		for (unsigned i=0; i<wnl.size(); i++) {
			watch &w = wnl[i];
			lit &implied = w.implied_lit;
			//if (vars[var(implied)].have() && vars[var(implied)].value == sign(implied))
			if (value(implied) == true)
				continue;
			if (is_ptr(w.this_cl)) {
				clause_ptr cl_ptr = w.this_cl.ptr;
				clause &c = db[cl_ptr];
				if (c.l[0] == ~l)
					c.l[0] = c.l[1], c.l[1] = ~l;
				implied = c.l[0];
				//if (vars[var(implied)].have() && vars[var(implied)].value == sign(implied)) {
				if (value(implied) == true) {
					// clause already satisfied
					continue;
				}
				unsigned j;
				for (j=2; j<c.header.size; j++) {
					lit k = c.l[j];
					//const var_desc &vk = vars[var(k)];
					//if (!vk.have() || vk.value == sign(k))
					if (value(k) != false)
						break;
				}
				if (j < c.header.size) {
					lit k = c.l[j];
					c.l[1] = k;
					c.l[j] = ~l;
					watches[k].push_back(w);
					w = wnl.back();
					wnl.pop_back();
					i--;
					continue;
				}
			}
			//if (v_implied.have()) {
			//if (vars[var(implied)].have()) {
			if (have(implied)) {
#if 0
				assert(vars[var(implied)].value != sign(implied));
				lit tmp[2];
				const lit *a, *b;
				deref(w.this_cl, tmp, &a, &b);
				for (; a<b; a++)
					assert(vars[var(*a)].have() && vars[var(*a)].value != sign(*a));
				// other watched lit set to false
#endif
				rw = &w;
				break;
			}
#if 0
			{
				lit tmp[2];
				const lit *a, *b;
				unsigned unset = 0, pos = 0, neg = 0, total = 0;
				deref(w.this_cl, tmp, &a, &b);
				for (; a<b; a++, total++)
					if (!vars[var(*a)].have()) {
						assert(*a == implied);
						unset++;
					} else if (vars[var(*a)].value == sign(*a))
						pos++;
					else
						neg++;
				assert(unset == 1);
				assert(pos + neg == total - 1);
			}
#endif
			assert(var(implied) != var(l));
			assign(w);
			//units.emplace_back(w);
			//vars[var(implied)] = var_desc{(status)sign(implied),(uint32_t)units.size()};

			/* Basic algorithm:
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
	}
	stats->propagations += (unit_ptr-up) + (rw != nullptr);
	stats->pt += t.get();
	return rw;
}

lit ksat::next_decision() const
{
#if 1
	if (lit_heap)
		while (lit_heap->valid) {
			lit l = {lit_heap->pop()};
			if (!have(l))
				return l;
		}
	else {
		int32_t max = -1;
#if 1
		for (uint32_t v=0; v<n_active; v++) {
			uint32_t w = active[v];
			if (have(w))
				continue;
			if (max < 0 || vsids[max] < vsids[2*w])
				max = 2*w;
			if (vsids[max] < vsids[2*w+1])
				max = 2*w+1;
		}
#elif 1
		uint32_t n = decisions.empty() ? units.size() : decisions.front();
		for (uint32_t v=0; v<n_active; v++) {
			uint32_t w = active[v];
			if (vars[w].have()) {
				if (vars[w].trail_pos_plus1 <= n)
					active[v--] = active[--n_active];
			} else {
				if (max < 0 || vsids[max] < vsids[2*w])
					max = 2*w;
				if (vsids[max] < vsids[2*w+1])
					max = 2*w+1;
			}
		}
#else
		for (uint32_t v=0; v<2*nvars; v++)
			if (!vars[var({v})].have() && (max < 0 || vsids[max] < vsids[v]))
				max = v;
#endif
		if (max >= 0)
			return {(uint32_t)max};
	}
#else
	for (uint32_t v=0; v<nvars; v++)
		if (!vars[v].have())
			return {2*v+!vars[v].value};
#endif
	return {2*nvars};
}

void ksat::trackback(uint32_t dlevel) // to including dlevel
{
#if 0
	for (uint32_t i=dlevel; i<decisions.size(); i++)
		vars[var(units[decisions[i]].implied_lit)].value ^= 0;
#endif
	for (uint32_t i=decisions[dlevel]; i<units.size(); i++) {
		vars[var(units[i].implied_lit)].value = INDET;
	//	vars[var(units[i].implied_lit)].trail_pos_plus1 = 0;
	}
	if (lit_heap) {
		uint32_t v = lit_heap_valid[dlevel];
		lit_heap_valid.resize(dlevel);
		lit_heap->restore(v);
	}
	units.resize(decisions[dlevel]);
	decisions.resize(dlevel);
	unit_ptr = units.size();
}
#if 0
int32_t ksat::resolve_conflict(const watch *w, std::vector<lit> (&v)[2], measurement &m) const
{
	lit clp[2];
	const lit *a, *b;
	uint32_t dec;
	deref(w->this_cl, clp, &a, &b);
	auto tp1 = [this](lit l){ return vars[var(l)].trail_pos_plus1; };
	auto td = [tp1,k=decisions.back()](lit l){ return tp1(l) > k; };
	auto gt = [tp1](lit a, lit b){ return tp1(a) > tp1(b); };
	auto lit2tp = [tp1](lit l){ return lit{tp1(l) << 1 | sign(l)}; };
	auto tp2lit = [this](lit l){ return lit{var(units[var(l)-1].implied_lit)<<1 | sign(l)}; };
	lit l = w->implied_lit;
	v[0].clear();
	v[1].clear();
	v[1].reserve(b-a);
	v[1].push_back(lit2tp(a[0] == l ? a[1] : a[0]));
	for (a += 2; a < b; a++) {
		if (td(*a))
			v[1].push_back(lit2tp(*a));
		else
			v[0].push_back(*a);
	}
	assert(v[1].size() >= 1);
	l = lit2tp(l);
	goto in;
	while (v[1].size() > 1) {
#if 0
		fprintf(stderr, "dl %zu:%u resolve1:", decisions.size(), decisions.back());
		for (int i=1; i>=0; i--) {
			fprintf(stderr, " %zu:", v[i].size());
			for (lit k : v[i])
				fprintf(stderr, " %ld[%u]", lit_to_dimacs(i ? tp2lit(k) : k), vars[var(i ? tp2lit(k) : k)].trail_pos_plus1-1);
		}
		fprintf(stderr, "\n");
#endif
		{
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
		else if (0 && v[1].size() > decisions.size()) {
			v[1].clear();
			return -1;
		}
		v[1][max] = v[1].back();
		}
		v[1].pop_back();
in:
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
		fprintf(stderr, "dl %zu:%u resolved to", decisions.size(), decisions.back());
		for (int i=1; i>=0; i--) {
			fprintf(stderr, " %zu:", v[i].size());
			for (lit k : v[i])
				fprintf(stderr, " %ld[%u]", lit_to_dimacs(i ? tp2lit(k) : k), vars[var(i ? tp2lit(k) : k)].trail_pos_plus1-1);
		}
		fprintf(stderr, "\n");
#endif
#if 0
		if (!(m.n & 0x3ff)) {
			fprintf(stderr, "%8lu %8zu %8zu        \r", m.n, v[1].size(), v[0].size());
			fflush(stderr);
		}
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
	uint32_t max_tp1 = v[0].empty() ? 0 : tp1(v[0][0]);
	for (dec=decisions.size(); dec>0; dec--)
		if (max_tp1 > decisions[dec-1])
			break;
	return dec;
}
#endif
template <bool use_merge_res>
std::pair<int32_t,int32_t> ksat::resolve_conflict2(const watch *w, std::vector<lit> (&v)[2], measurement &m) const
{
	const int32_t n = decisions.back();
	auto tp = [this](lit l) -> int32_t { return vars[var(l)].trail_pos(); };

	lit tmp[2];
	const lit *a, *b;
	avail.resize(units.size());
	avail.clear();
	deref(w->this_cl, tmp, &a, &b);
	for (; a<b; a++) {
//		fprintf(stderr, "adding1 %u\n", tp(*a));
		assert(value(*a) == false);
		avail.set(tp(*a));
	}
	int32_t p = avail.max_bit(), q;
	bool have_merged_lit = false;
	std::pair<int32_t,int32_t> ret;
	ret.first = -1;

	auto assertion = [this](lit l){ assert(value(l) == false); return l; };

	auto collect_lits = [this,n,assertion](int32_t p, vector<lit> &v, const bitset &av, bool is_merge_res){
		assert(p >= n);
		v.clear();
		v.push_back(assertion(~units[p].implied_lit));
		int32_t dec = 0, r = p;
		for (uint32_t i=1; (r = av.max_bit_lt(r)) >= 0; i++) {
			assert(r < n || (i == 1 && is_merge_res));
			if (i == (is_merge_res ? 2 : 1))
				for (dec=decisions.size(); dec>0; dec--)
					if ((uint32_t)r >= decisions[dec-1])
						break;
			//if (i >= (is_merge_res ? 2 : 1))
			//	assert(p < n);
			//else
			//	assert(p >= n);
			v.push_back(assertion(~units[r].implied_lit));
		//	av.unset(r);
		}
		assert(dec >= 0);
		return dec;
	};

	while (1) {
		assert(p >= n);
		avail.unset(p);
//		assert(avail.max_bit(p) == avail.max_bit_lt(p));
		q = avail.max_bit_lt(p); /* TODO? use .max_bit(n,p) */
//		fprintf(stderr, "unset %u, next q: %d\n", p, q);
		if (q < n) {
			ret.second = collect_lits(p, v[1], avail, false);
			return ret;
		}
		if (use_merge_res && have_merged_lit &&
		#if 1
		    avail.is_zero(n,q)
		#else
		    avail.bitcount(n,q) <= 2 - 2 /* -2: p and q on conflict level*/
		#endif
		) {
			ret.first = collect_lits(p, v[0], avail, true);
		}
		deref(units[p].this_cl, tmp, &a, &b);
		for (; a<b; a++) {
			if (tp(*a) == p) /* TODO: skip, is 1st or 2nd */
				continue;
//			fprintf(stderr, "adding2 %u\n", tp(*a));
			assert(tp(*a) < p);
			if (tp(*a) > q)
				q = tp(*a);
			if (use_merge_res && tp(*a) >= n && !have_merged_lit)
				have_merged_lit = avail.get(tp(*a));
			avail.set(tp(*a));
		}
		p = q;
		m.tick();
	}
}

uint32_t ksat::analyze(const watch *w, vector<lit> (&v)[2], struct statistics *stats) const
{
	std::pair<int32_t,int32_t> dec = {-1,-1};
	measurement m;
	m.start();

	//if ((nvars-decisions.front())/(unit_ptr+1-decisions.back()) > decisions.size())
	if (decisions.size() > 1)
		dec = resolve_conflict2<true>(w, v, m);
	else
		dec = resolve_conflict2<false>(w, v, m);

	m.stop();
	stats->resolutions += m.n;
	stats->rt += m.t;
#if 0
	fprintf(stderr, "dl %zu:%u resolution done in %luus, %lu steps, resulted in clause of size %zu on dl %d\n",
	        decisions.size(), decisions.back(), m.t, m.n, v[1].size(), dec);
#endif
	if (dec.first < 0) { // cl.size() > decisions.size() || !vars[var(cl[most_recent_this_dl])].have()
		v[0].resize(decisions.size());
		for (uint32_t i=0; i<decisions.size(); i++)
			v[0][decisions.size()-1-i] = ~units[decisions[i]].implied_lit;
		dec.first = decisions.size()-1;
	}
	return std::min(dec.first, dec.second);
}

void ksat::assign(const watch &w)
{
	vars[var(w.implied_lit)] = var_desc{(status)sign(w.implied_lit),(uint32_t)units.size()+1};
	units.push_back(w);
}

void ksat::make_decision(lit d)
{
	assert(!have(d));
	decisions.push_back(units.size());
	// fprintf(stderr, "dl %zu: next decision %ld[%zu]\n", decisions.size(), lit_to_dimacs(d), units.size());
	assign({clause_proxy{.ptr=CLAUSE_PTR_NULL},d});
}

status ksat::run()
{
	vector<lit> cl[2];
	statistics stats(*this);
	bool do_vacuum = true; /* cleanups only on decision level 0 */
	status r = INDET;
	luby_seq luby(1 << 6);
	unsigned long next_restart = luby(); /* restart interval increments */
	unsigned long last_vacuum = 0;       /* helper to decide whether to clean up the clause db */
//	unsigned long last_vsids_adj = 0;
	timer st; /* measure timings of individual parts */
	while (1) {
		/* output statistics approx. every second */
		if (stats.t.get()-stats.last_out > 1000000)
			stats();

		/* propagate everything from unit_ptr to units.size() and check
		 * for a conflict w */
		if (const watch *w = propagate_units(&stats)) {
			++stats.conflicts;
			if (decisions.empty()) {
				/* conflict w/o decisions */
				unsat = true;
				r = FALSE;
				break;
			}
			/* analyze the conflict and determine clauses cl to learn */
			uint32_t decision_level = analyze(w, cl, &stats);
			st.start();
			/* check whether cl[0] subsumes cl[1] */
			bool inc = cl[1].size() >= cl[0].size() &&
			           includes(cl[1].begin(), cl[1].end(), cl[0].begin(), cl[0].end(),
			                    [this](lit a, lit b){ return -(int32_t)(vars[var(a)].trail_pos() - vars[var(b)].trail_pos()); });
			/* reset assignments made */
			trackback(decision_level);
			/* add learnt clauses to db */
			learn_clause(cl[0], &stats);
			if (!inc)
				learn_clause(cl[1], &stats);
			/* check whether to restart */
			if (stats.conflicts == next_restart) {
				if (decision_level)
					trackback(0);
				do_vacuum = units.size() > last_vacuum;
				stats.restarts++;
				next_restart += (++luby)();
				dec_all(); /* decrease VSIDS values */
			}
			stats.tt += st.get();
			/* try propagation again with new clauses attached */
			continue;
		}
		/* clean up clause db if necessary */
		if (do_vacuum) {
			assert(decisions.empty());
			vacuum();
			do_vacuum = false;
			last_vacuum = units.size();
		}
		/* make a new decision */
		st.start();
		if (lit_heap)
			lit_heap_valid.push_back(lit_heap->valid);
		lit d = next_decision(); /* via VSIDS */
		stats.dt += st.get();
		if (var(d) >= nvars) {
			/* no decision possible, all variables assigned */
			r = TRUE;
			break;
		}
		stats.n_decisions++;
		make_decision(d);
	}
	stats();
	fprintf(stderr, "%s\n", r == TRUE ? "SAT" : r == FALSE ? "UNSAT" : "INDET");
	return r;
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
#elif 1
	if (value(l) == true)
		return true;
	if (have(l))
		return false;
#else
	auto &v = vars[var(l)];
	if (v.have() && v.value == sign(l))
		return true;
	if (v.have())
		return false;
#endif
#if 1
	assign({p,l});
#else
	units.push_back({p,l});
	v = var_desc{(status)sign(l),(uint32_t)units.size()};
#endif
	return true;
}

void ksat::learn_clause(vector<lit> &cl, struct statistics *stats)
{
	unsigned j=0;
	stats->learnt++;
	stats->learnt_lits += cl.size();
#if 0
	fprintf(stderr, "adding clause");
	unsigned i;
	for (i=0; i<std::min((uint32_t)cl.size(), 5U); i++)
		fprintf(stderr, " %ld[%d]", lit_to_dimacs(cl[i]), vars[var(cl[i])].trail_pos_plus1-1);
	if (i < cl.size())
		fprintf(stderr, " ...");
	fprintf(stderr, "\n");
#endif
#if 1
	for (unsigned i=0; j<2 && i<cl.size(); i++)
		if (!have(cl[i])) {
			assert(j == i);
			swap(cl[j++], cl[i]);
		} else
			;//assert(vars[var(cl[i])].value != sign(cl[i]));
#else
	j = 1;
#endif
	if (cl.size() < 2) {
		assert(decisions.empty());
		if (cl.size() == 0 || (assert(j == 1), !add_unit(cl[0])))
			unsat = true;
		return;
	}
	for (lit l : cl)
		reg(l);
	clause_proxy p;
	/* 0 and especially 1 must be those assigned latest!!! */
#if 0
	#if 1
	for (unsigned k=2; k<cl.size(); k++)
		if (vars[var(cl[k-1])].have()) {
			assert(vars[var(cl[k])].have());
			assert(vars[var(cl[k])].trail_pos_plus1 < vars[var(cl[k-1])].trail_pos_plus1);
		}
	#else
	unsigned w = 1;
	for (unsigned k=2; k<cl.size(); k++)
		if (vars[var(cl[k])].trail_pos_plus1 >
		    vars[var(cl[w])].trail_pos_plus1) {
			assert(0);
			w = k;
		}
	swap(cl[1], cl[w]);
	#endif
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
		if (!have(c[i]))
			swap(c[j++], c[i]);
		else
			sat |= value(c[i]);
	if (c.size() >= 2) {
		clause_proxy p;
		for (lit l : c)
			reg(l);
		if (c.size() == 2) {
			p.l[0] = c[0] | CLAUSE_PROXY_BIN_MASK;
			p.l[1] = c[1] | CLAUSE_PROXY_BIN_MASK;
		} else {
#if 1
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
	fprintf(stderr, "%u chunks (cached: %u):", db.chunks.size(), 0/*db.chunks.init_cap()*/);
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

}
