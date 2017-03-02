
#ifndef KSAT_HH
#define KSAT_HH

#include "common.h"

#include <cassert>
#include <cstdlib>	/* abs() */
#include <cinttypes>	/* uint32_t */
#include <vector>
#include <forward_list>

#include "util.hh"

// typedef uint32_t var;
// typedef uint32_t lit; /* 2*var + phase; phase ? pos : neg */

struct lit {
	uint32_t v; /* 2*var + phase; phase ? pos : neg */

	operator uint32_t() const { return v; }
};

inline lit      operator~(lit l) { return { l.v ^ 1U }; }
inline uint32_t var(lit l) { return l.v >> 1; }
inline bool     sign(lit l) { return l.v & 1U; }

#define LOG_NUM_VARS	30U

struct clause_ptr {
	uint32_t chunk_idx;
	uint32_t offset;

	explicit operator bool() const { return chunk_idx || offset; }
};

static constexpr clause_ptr CLAUSE_PTR_NULL = { 0U, 0U };

inline bool operator==(const struct clause_ptr &a, const struct clause_ptr &b)
{
	return a.offset == b.offset && a.chunk_idx == b.chunk_idx;
}

struct clause {
	struct clause_header {
		uint32_t size : LOG_NUM_VARS;
		uint32_t learnt : 1;
		uint32_t remove : 1;
	} header;
	lit l[]; /* first two are watched */

	lit * begin() { return l; }
	lit * end()   { return l + header.size; }

	const lit *  begin() const { return l; }
	const lit *  end()   const { return l + header.size; }
	const lit * cbegin() const { return l; }
	const lit * cend()   const { return l + header.size; }
};

#define LIT_SPARE_BIT		((uint32_t)1 << 31)
#define CLAUSE_PROXY_BIN_MASK	LIT_SPARE_BIT

/* a clause_ptr has the same size as two literals, so in case of binary clauses,
 * which are stored solely in the watch list, use the pointer itself to store
 * the literals of the binary clause. */
union clause_proxy {
	uint32_t l[2];
	clause_ptr ptr;

	unsigned spare() /* 2 bits: 4 states: 11: !is_ptr; xy: unused */
	{
		return !!(l[0] & CLAUSE_PROXY_BIN_MASK) << 1 |
		       !!(l[1] & CLAUSE_PROXY_BIN_MASK) << 0;
	}
	explicit operator bool() const;
};

static inline bool is_ptr(const clause_proxy &p)
{
	return !(p.l[0] & p.l[1] & CLAUSE_PROXY_BIN_MASK);
}

inline clause_proxy::operator bool() const { return !is_ptr(*this) || ptr; }

struct watch {
	clause_proxy this_cl;
	lit implied_lit;

	unsigned spare() /* 3 bits; 6 states: 11z: !is_ptr(this_cl); xyz: unused */
	{
		return this_cl.spare() << 1 |
		       !!(implied_lit & LIT_SPARE_BIT) << 0;
	}
};

struct clause_db {

	struct chunk {
		uint32_t const size;
		uint32_t valid;
		uint32_t *v;

		explicit chunk(uint32_t sz);
		chunk(const chunk &) = delete;
		chunk(chunk &&);
		~chunk() { clear(); }
		clause & operator[](uint32_t off) const;
		chunk & operator=(chunk) = delete;
		void clear() { delete[] v; v = nullptr; }
	};

	struct iterator {

		const clause_db &db;
		clause_ptr p;

		iterator(const clause_db &db, clause_ptr p) : db(db), p(p) {}

		iterator & operator++()
		{
			if ((p.offset += db[p].header.size + 1) >= db.chunks[p.chunk_idx].valid) {
				p.chunk_idx++;
				p.offset = 0;
			}
			return *this;
		}

		const clause & operator*() const { return db[p]; }
		const clause * operator->() const { return std::addressof(**this); }

		bool operator==(const iterator &o) const { return p == o.p; }
		bool operator!=(const iterator &o) const { return !(*this == o); }
	};

	/* usually few chunks, try to keep their descriptors in the cache line
	 * of this clause_db instance */
	std::vector<chunk> chunks;

	clause_db();
	clause_db(const clause_db &) = delete;
	clause_db(clause_db &&) = default;

	clause_db & operator=(clause_db) = delete;

	clause_ptr alloc(uint32_t size);
	clause_ptr add(uint32_t size, bool learnt);
	void       del(clause_ptr);
	clause &   operator[](clause_ptr p) const;

	iterator begin() const { return iterator(*this, {0,1}); }
	iterator end()   const { return iterator(*this, {(uint32_t)chunks.size(),0}); }

	void deref(const clause_proxy &p, lit *tmp, const lit **start, const lit **end) const
	{
		if (is_ptr(p)) {
			const clause &cp = (*this)[p.ptr];
			*start = cp.begin();
			*end = cp.end();
		} else {
			tmp[0] = {p.l[0] & ~CLAUSE_PROXY_BIN_MASK};
			tmp[1] = {p.l[1] & ~CLAUSE_PROXY_BIN_MASK};
			*start = tmp;
			*end = tmp+2;
		}
	}

	void deref(const clause_proxy &p, lit *tmp, lit **start, lit **end) const
	{
		if (is_ptr(p)) {
			clause &cp = (*this)[p.ptr];
			*start = cp.begin();
			*end = cp.end();
		} else {
			tmp[0] = {p.l[0] & ~CLAUSE_PROXY_BIN_MASK};
			tmp[1] = {p.l[1] & ~CLAUSE_PROXY_BIN_MASK};
			*start = tmp;
			*end = tmp+2;
		}
	}
};

struct assignments {

	uint8_t *data = nullptr;

	~assignments() { free(data); }

	void init(uint32_t nvars)
	{
		data = (uint8_t *)calloc((nvars+3)/4, 1);
	}

	template <typename R>
	struct _ptr {
		R &p;
		uint8_t shift;

		operator unsigned() const { return (p >> shift) & 3; }
		unsigned operator|=(unsigned v) { return ((p |= v << shift) >> shift) & 3; }
	};

	template <typename R>
	struct _lptr {
		R &p;
		uint8_t shift;
		unsigned mask;

		operator unsigned() const { return (p >> shift) & 3; }
		bool have() const { return *this != 0; }
		bool same() const { return *this & mask; }
		bool other() const { return *this & (mask ^ 3); }
		bool both() const { return *this == 3; }
		void set() const { p |= mask << shift; }
	};

	typedef const _ptr<uint8_t> ptr;
	typedef const _ptr<const uint8_t> cptr;

	typedef const _lptr<uint8_t> lptr;
	typedef const _lptr<const uint8_t> clptr;

	ptr operator[](uint32_t var) { return { data[var/4], (uint8_t)((var & 3) << 1) }; }
	cptr operator[](uint32_t var) const { return { data[var/4], (uint8_t)((var & 3) << 1) }; }

	lptr operator[](lit l) { return { data[var(l)/4], (uint8_t)((var(l) & 3) << 1), 1U << sign(l) }; }
	clptr operator[](lit l) const { return { data[var(l)/4], (uint8_t)((var(l) & 3) << 1), 1U << sign(l) }; }
};

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

struct bitset {

	static constexpr size_t word_bits() { return sizeof(unsigned long)*CHAR_BIT; }

	std::vector<unsigned long> v;

	bitset() {}
	explicit bitset(uint32_t n) : v((n+word_bits()-1)/word_bits()) {}

	void clear() { memset(v.data(), 0, sizeof(unsigned long) * v.size()); }

	void set(uint32_t p) { v[p/word_bits()] |= 1UL << (p%word_bits()); }
	void unset(uint32_t p) { v[p/word_bits()] &= ~(1UL << (p%word_bits())); }
	bool get(uint32_t p) const { return v[p/word_bits()] & (1UL << (p%word_bits())); }
	int32_t max_bit() const
	{
		for (int32_t i=v.size(); i; i--)
			if (v[i-1])
				return i * word_bits() - (BSR(v[i-1])+1);
		return -1;
	}
	int32_t max_bit(uint32_t hint) const
	{
		for (int32_t i=hint/word_bits()+1; i; i--)
			if (v[i-1])
				return i * word_bits() - (BSR(v[i-1])+1);
		return -1;
	}
	int32_t max_bit_lt(uint32_t p) const
	{
		int32_t i = (p+word_bits()-1)/word_bits();
		if (!i)
			return -1;
		unsigned long w = v[i-1] & ~(~0UL << (p % word_bits()));
		if (w)
			return i * word_bits() - (BSR(w)+1);
		return i > 1 ? max_bit((i-2)*word_bits()) : -1;
	}
	void resize(uint32_t n) { v.resize((n+word_bits()-1)/word_bits()); }

	uint32_t bitcount(uint32_t a, uint32_t b) const
	{
		uint32_t r = 0;
		uint32_t lo = a/word_bits();
		uint32_t hi = (b+word_bits()-1)/word_bits();
		for (uint32_t i=lo; i<std::min((uint32_t)v.size(), hi); i++) {
			unsigned long w = v[i];
			if (i == lo)
				w &= ~0UL << (a % word_bits());
			if (i == b/word_bits())
				w &= ~(~0UL << (b % word_bits()));
			r += __builtin_popcountl(w);
		}
		return r;
	}

	uint32_t is_zero(uint32_t a, uint32_t b)
	{
		unsigned long x = 0, y = 0, z = 0;
		uint32_t lo = a/word_bits();
		uint32_t hi = std::min(v.size(),(b+word_bits()-1)/word_bits());
		if (lo >= hi)
			return true;
		x = v[lo  ] &  (~0UL << (a % word_bits()));
		y = hi-1 == b/word_bits() ? v[hi-1] & ~(~0UL << (b % word_bits())) : v[hi-1];
		z = (lo == b/word_bits()) ? x & y : x | y;
		for (uint32_t i=lo+1; !z && i<hi-1; i++)
			z |= v[i];
		return !z;
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

class ksat {

	struct var_desc {
		uint32_t value : 1;
		uint32_t trail_pos_plus1 : LOG_NUM_VARS;

		var_desc(bool value=false, uint32_t trail_pos_plus1=0)
		: value(value), trail_pos_plus1(trail_pos_plus1) {}

		bool have() const { return trail_pos_plus1 > 0; }
	};

	clause_db db;

	var_desc *vars;
//	assignments assigns;     // assignment per variable
	vec<watch> *watches;     // watch lists
	std::vector<watch> units;  // trail, including reasons (if implied)
	std::vector<uint32_t> decisions; // indices of trail which start a new decision level
	uint32_t unit_ptr = 0;   // current position in trail

	uint32_t nvars;          // constant number of instance variables

	std::vector<uint32_t> lit_heap_valid;
	mutable bin_inv_heap *lit_heap = nullptr;
	mutable uint32_t *active;
	mutable uint32_t n_active;
	mutable uint32_t *vsids;
	void reg(lit a) const;
	void dec_all() const;

	mutable bitset avail;

	lit next_decision() const;
	uint32_t analyze(const watch *w, std::vector<lit> (&v)[2], unsigned long *, unsigned long *, unsigned long *) const;
	void add_clause0(std::vector<lit> &);
	int32_t resolve_conflict(const watch *w, std::vector<lit> (&v)[2], measurement &m) const;
	template <bool>
	std::pair<int32_t,int32_t> resolve_conflict2(const watch *w, std::vector<lit> (&v)[2], measurement &m) const;
	void trackback(uint32_t dlevel);

	bool add_unit(lit l, const clause_proxy &p=clause_proxy{.ptr=CLAUSE_PTR_NULL});

	void deref(const clause_proxy &cp, lit *tmp, const lit **a, const lit **b) const { db.deref(cp, tmp, a, b); }

	void vacuum();

	struct bin_cl_itr {

		uint32_t tmp_cl[3];

		const ksat &sat;
		unsigned pos_idx = 0;

		bin_cl_itr(const ksat &sat, uint32_t pos)
		: tmp_cl{2,pos}, sat(sat)
		{ skip_non_bin(); }

		uint32_t & pos()       { return tmp_cl[1]; }
		uint32_t   pos() const { return tmp_cl[1]; }

		void skip_non_bin()
		{
			for (; pos() < 2*sat.nvars; ++pos(), pos_idx=0)
				for (; pos_idx < sat.watches[pos()].size(); pos_idx++) {
					watch &w = sat.watches[pos()][pos_idx];
					if (!is_ptr(w.this_cl) && pos() < w.implied_lit) {
						tmp_cl[2] = w.implied_lit;
						return;
					}
				}
		}

		bin_cl_itr & operator++()
		{
			++pos_idx;
			skip_non_bin();
			return *this;
		}

		const clause & operator*() const
		{
			return *reinterpret_cast<const clause *>(tmp_cl);
		}
		const clause * operator->() const { return std::addressof(**this); }

		bool operator==(const bin_cl_itr &o) const { return pos() == o.pos() && pos_idx == o.pos_idx; }
		bool operator!=(const bin_cl_itr &o) const { return !(*this == o); }
	};

	const watch * propagate_units(unsigned long *, unsigned long *, unsigned long *);

public:
	ksat(const ksat &) = delete;
	ksat() {}
	~ksat();

	ksat & operator=(const ksat &) = delete;

	bool unsat = false; /* shortcut for \exists v : vars[v].implied == 3 */

	int  run();
	void init(uint32_t nvars);
	void add_clause(std::vector<lit> &c);
	void stats(int verbosity);

	uint32_t num_vars() const { return nvars; }

	unsigned get_assign(uint32_t v) const { return vars[v].have() ? 1U << vars[v].value : 0; }

	typename decltype(units)::const_iterator units_begin() const { return units.begin(); }
	typename decltype(units)::const_iterator units_end()   const { return units.end(); }
	size_t                                   units_size()  const { return units.size(); }

	bin_cl_itr binary_clauses_begin() const { return bin_cl_itr(*this, 0); }
	bin_cl_itr binary_clauses_end()   const { return bin_cl_itr(*this, 2*nvars); }

	clause_db::iterator large_clauses_begin() const { return db.begin(); }
	clause_db::iterator large_clauses_end()   const { return db.end(); }

	typedef concat_itr<const clause,bin_cl_itr,clause_db::iterator> clause_itr;

	class cl_ref {
		const ksat &sat;
	public:
		cl_ref(const ksat &sat) : sat(sat) {}

		clause_itr begin() const
		{
			return {
				sat.binary_clauses_begin(),
				sat.binary_clauses_end(),
				sat.large_clauses_begin()
			};
		}

		clause_itr end() const
		{
			return {
				sat.binary_clauses_end(),
				sat.binary_clauses_end(),
				sat.large_clauses_end()
			};
		}
	};

	cl_ref clauses() const { return { *this }; }
};

static inline lit dimacs_to_lit(long v)
{
	uint32_t av = std::abs(v) - 1;
	return { av << 1 | (v > 0) };
}

static inline long lit_to_dimacs(lit l)
{
	long v = (l.v >> 1) + 1;
	return (l.v & 1) ? v : -v;
}

#endif
