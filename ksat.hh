/*
 * ksat.hh
 *
 * Copyright 2017 Franz Brauße <brausse@informatik.uni-trier.de>
 *
 * This file is part of ksat.
 * See the LICENSE file for terms of distribution.
 */

#ifndef KSAT_HH
#define KSAT_HH

#include "common.h"

#include <cassert>
#include <cstdlib>	/* abs() */
#include <cinttypes>	/* uint32_t */
#include <vector>
#include <array>
#include <memory>	/* std::unique_ptr */

#ifndef CACHE_LINE_SZ
# define CACHE_LINE_SZ	64
#endif

#define NEXT_MULTIPLE(off,algn)	(((off)+(algn)-1)/(algn)*(algn))

namespace ksat_ns {

template <typename T>
static constexpr size_t vec_head_sz() { return sizeof(T*) + 2*sizeof(uint32_t); }

template <typename T,size_t cache_line_sz = CACHE_LINE_SZ>
class vec {

//	static_assert(std::is_pod<T>::value, "T needs to be POD");

	static const size_t head_sz = vec_head_sz<T>();
	static_assert(head_sz % alignof(T) == 0, "T needs proper alignment");

	T *body;
	uint32_t sz, cap;
	alignas(T) char init[((cache_line_sz-head_sz%cache_line_sz)%cache_line_sz)];

	T * at(uint32_t idx)
	{
		return idx < init_cap()
		       ? reinterpret_cast<T *>(init + idx * sizeof(T))
		       : body + (idx-init_cap());
	}

	const T * at(uint32_t idx) const
	{
		return idx < init_cap()
		       ? reinterpret_cast<const T *>(init + idx * sizeof(T))
		       : body + (idx-init_cap());
	}

public:
	typedef       T              value_type;
	typedef       uint32_t       size_type;
	typedef       value_type &   reference;
	typedef const value_type &   const_reference;
	typedef       value_type *   pointer;
	typedef const value_type *   const_pointer;

	template <typename V>
	struct itr {
		V &v;
		size_type idx;

		itr(V &v, size_type idx) : v(v), idx(idx) {}

		itr & operator++()    { ++idx; return *this; }
		itr   operator++(int) { itr cpy = *this; ++*this; return cpy; }
		itr & operator+=(size_type n) { idx += n; return *this; }

		const T & operator* () const { return v[idx]; }
		const T * operator->() const { return &**this; }

		bool operator==(const itr &o) const { return idx == o.idx; }
		bool operator!=(const itr &o) const { return idx != o.idx; }
	};

	struct iterator : public itr<vec> {
		using itr<vec>::itr;
		      T & operator* ()       { return itr<vec>::v[itr<vec>::idx]; }
		      T * operator->()       { return &**this; }
	};

	typedef       itr<const vec> const_iterator;

	static constexpr size_type init_cap() { return sizeof(init)/sizeof(T); }

	vec() : body(nullptr), sz(0), cap(init_cap()) {}
	explicit vec(size_type n) : vec()
	{
		reserve(n);
		if (!std::is_pod<T>::value)
			while (sz < n)
				new (at(sz++)) T();
	}
	~vec()
	{
		if (!std::is_pod<T>::value)
			clear();
		free(body);
	}
	vec(const vec &) = delete;
	vec(vec &&o) : body(o.body), sz(o.sz), cap(o.cap)
	{
		if (std::is_pod<T>::value)
			memcpy(init, o.init, sizeof(init));
		else
			for (size_type i=0; i<std::min(sz,init_cap()); i++)
				new (at(i)) T(std::move(o[i]));
		o.body = nullptr;
		o.sz = 0;
		o.cap = init_cap();
	}

	vec & operator=(vec) = delete;

	void reserve(size_type n)
	{
		if (n <= init_cap())
			return;
		if (std::is_pod<T>::value)
			body = (T *)realloc(body, ((cap = n) - init_cap()) * sizeof(T));
		else {
			T *tmp = (T *)malloc(((cap = n) - init_cap()) * sizeof(T));
			std::swap(tmp, body);
			for (size_type i=init_cap(); i<sz; i++)
				new (at(i)) T(std::move(tmp[i-init_cap()]));
			free(tmp);
		}
	}

	void resize(size_type n)
	{
		reserve(std::max(n, 2*(sz+1)));
		if (!std::is_pod<T>::value)
			for (size_type i=sz; i<n; i++)
				new (at(i)) T();
		sz = n;
	}

	T & operator[](size_type idx)
	{
		return *at(idx);
	}

	const T & operator[](size_type idx) const
	{
		return *at(idx);
	}

	      T & back()       { return (*this)[size()-1]; }
	const T & back() const { return (*this)[size()-1]; }

	iterator       begin()        { return iterator(*this, 0); }
	iterator       end()          { return iterator(*this, sz); }
	const_iterator begin()  const { return const_iterator(*this, 0); }
	const_iterator end()    const { return const_iterator(*this, sz); }
	const_iterator cbegin() const { return const_iterator(*this, 0); }
	const_iterator cend()   const { return const_iterator(*this, sz); }

	bool empty() const { return !sz; }
	size_type size() const { return sz; }
	size_type capacity() const { return cap; }

	void push_back(const T &t)
	{
		if (sz >= cap)
			reserve(2*(sz+1));
		(*this)[sz++] = t;
	}

	template <typename... Args>
	void emplace_back(Args &&... args)
	{
		if (sz >= cap)
			reserve(2*(sz+1));
		new (at(sz++)) T(std::forward<Args...>(args...));
	}

	void pop_back() { at(--sz)->~T(); }

	void clear()
	{
		if (std::is_pod<T>::value)
			sz = 0;
		else
			while (!empty())
				pop_back();
	}
};

template <typename T> using nc_vec = vec<T,vec_head_sz<T>()>;

template <typename V, typename I1, typename I2>
struct concat_itr {

	I1 i1s;
	const I1 i1e;
	I2 i2s;

	concat_itr(I1 i1s, I1 i1e, I2 i2s) : i1s(i1s), i1e(i1e), i2s(i2s) {}

	V & operator*() const { return i1s != i1e ? *i1s : *i2s; }
	V * operator->() const { return std::addressof(**this); }

	concat_itr & operator++()
	{
		if (i1s != i1e)
			++i1s;
		else
			++i2s;
		return *this;
	}

	bool operator!=(const concat_itr &o) const { return i1s != o.i1s || i2s != o.i2s; }
	bool operator==(const concat_itr &o) const { return !(*this != o); }
};

/* as per Knuth */
class luby_seq {
	const uint32_t factor;
	uint32_t un = 1, vn = 1;
public:
	explicit luby_seq(uint32_t factor) : factor(factor) {}
	uint32_t operator()() const { return factor*vn; }
	luby_seq & operator++()
	{
		if ((un & -un) == vn) {
			un++;
			vn = 1;
		} else
			vn <<= 1;
		return *this;
	}
};

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

	/* TODO: usually few chunks, try to keep their descriptors in the cache line
	 * of this clause_db instance: use ksat::vec */
	vec<chunk> chunks;

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

	struct ritr {
		const bitset &bs;
		int32_t p;

		ritr(const bitset &bs, int32_t p) : bs(bs), p(bs.max_bit(p)) {}
		ritr(const bitset &bs) : bs(bs), p(bs.max_bit()) {}

		ritr & operator++() { p = bs.max_bit_lt(p); return *this; }
		ritr   operator++(int) { ritr tmp = *this; ++*this; return tmp; }

		const int32_t & operator*() const { return p; }
		const int32_t * operator->() const { return std::addressof(**this); }

		bool operator==(const ritr &o) const { return p == o.p; }
		bool operator!=(const ritr &o) const { return !(*this == o); }
	};

	static constexpr size_t word_bits() { return sizeof(unsigned long)*CHAR_BIT; }

	std::vector<unsigned long> v;

	bitset() {}
	explicit bitset(uint32_t n) : v((n+word_bits()-1)/word_bits()) {}

	void clear() { memset(v.data(), 0, sizeof(unsigned long) * v.size()); }

	ritr rbegin() const { return { *this }; }
	ritr rend  () const { return { *this, -1 }; }

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
		uint32_t i = (p+word_bits()-1)/word_bits();
		if (!i)
			return -1;
		unsigned long w = v[i-1];
		if (i-1 == p/word_bits())
			w &= ~(~0UL << (p % word_bits()));
		if (w)
			return i * word_bits() - (BSR(w)+1);
		return i > 1 ? max_bit((i-2)*word_bits()) : -1;
	}
	int32_t max_bit_in(uint32_t a, uint32_t b)
	{
		uint32_t lo = a/word_bits();
		uint32_t hi = (b+word_bits()-1)/word_bits();
		for (uint32_t i=std::min((uint32_t)v.size(), hi); i>lo; i--) {
			unsigned long w = v[i-1];
			if (i-1 == lo)
				w &= ~0UL << (a % word_bits());
			if (i-1 == b/word_bits())
				w &= ~(~0UL << (b % word_bits()));
			if (w)
				return i * word_bits() - (BSR(w)+1);
		}
		return -1;
	}
	void resize(uint32_t n) { v.resize((n+word_bits()-1)/word_bits()); }
	void reserve(uint32_t n) { v.reserve((n+word_bits()-1)/word_bits()); }

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

	uint32_t is_zero(uint32_t a, uint32_t b) const
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

template <typename> struct bin_inv_heap;
struct statistics;

enum status {
	FALSE = false, TRUE = true, INDET,
};
#if 0
static constexpr bool operator==(status a, bool b) { return (unsigned)a == b; }
static constexpr bool operator==(bool a, status b) { return   b == a; }

static constexpr bool operator!=(status a, bool b) { return !(a == b); }
static constexpr bool operator!=(bool a, status b) { return   b != a ; }
#endif
static constexpr bool valid(status a) { return !(a & INDET); }

class run_context;

class ksat {

	friend struct statistics;
	friend class run_context;

	struct var_desc {
		status value : 2;
		uint32_t trail_pos_plus1 : LOG_NUM_VARS;

		var_desc(status value=INDET, uint32_t trail_pos_plus1=0)
		: value(value), trail_pos_plus1(trail_pos_plus1) {}

		bool have() const
		{
			//assert((trail_pos_plus1 > 0) ^ (value == INDET));
			// return trail_pos_plus1 > 0;
			return valid(value);
		}
		uint32_t trail_pos() const { return trail_pos_plus1 - 1; }
	};
	static_assert(sizeof(var_desc) == sizeof(uint32_t), "struct var_desc broken");

	struct vsids_le {
		const std::vector<uint32_t> &keys;
		bool operator()(uint32_t a, uint32_t b) const { return keys[a] >= keys[b]; }
	};

	clause_db db;

	nc_vec<var_desc> vars;
//	assignments assigns;     // assignment per variable
	nc_vec<vec<watch>> watches;     // watch lists
	std::vector<watch> units;  // trail, including reasons (if implied)
	std::vector<uint32_t> decisions; // indices of trail which start a new decision level
	uint32_t unit_ptr = 0;   // current position in trail

	uint32_t nvars;          // constant number of instance variables

	nc_vec<uint32_t> lit_heap_valid;
	bin_inv_heap<vsids_le> *lit_heap = nullptr;
	nc_vec<uint32_t> active;
	uint32_t n_active = 0;
	mutable std::vector<uint32_t> vsids;

	mutable bitset avail, simp;

	bool marked(uint32_t tp) const;

	//status value(uint32_t v) const { return vars[v].have() ? (status)vars[v].value : INDET; }
	//status value(lit l) const { return vars[var(l)].have() ? (status)(vars[var(l)].value == sign(l)) : INDET; }
	status value(uint32_t v) const { return vars[v].value; }
	status value(lit l) const
	{
	//	unsigned r = (unsigned)value(var(l)) ^ !sign(l);
	//	return r & 2 ? INDET : (status)r;
		return (status)(value(var(l)) ^ !sign(l));
	}
	bool   have(uint32_t v) const { return valid(value(v)); }
	bool   have(lit l) const { return have(var(l)); }

	bool unsat = false;

	void reg(lit a) const;
	void dec_all() const;

	struct res_info {
		int32_t dlvl;
		int32_t lbd;
		uint32_t deleted_lits;
	};

	template <bool>
	std::array<res_info,2> resolve_conflict2(const watch *w,
	                                         std::vector<lit> (&v)[2],
	                                         measurement &m) const;
	bool add_unit(lit l, const clause_proxy &p=clause_proxy{.ptr=CLAUSE_PTR_NULL});

	void assign(const watch &w);

	void deref(const clause_proxy &cp, lit *tmp, const lit **a, const lit **b) const
	{ db.deref(cp, tmp, a, b); }

	struct bin_cl_itr {

		uint32_t tmp_cl[3];

		const ksat &sat;
		unsigned pos_idx = 0;

		bin_cl_itr(const ksat &sat, uint32_t pos)
		: tmp_cl{2,pos}, sat(sat)
		{ skip_non_bin(); }

		uint32_t & pos()       { return tmp_cl[1]; }
		uint32_t   pos() const { return tmp_cl[1]; }

		void skip_non_bin();
		bin_cl_itr & operator++();

		const clause & operator*() const
		{
			return *reinterpret_cast<const clause *>(tmp_cl);
		}
		const clause * operator->() const { return std::addressof(**this); }

		bool operator==(const bin_cl_itr &o) const { return pos() == o.pos() && pos_idx == o.pos_idx; }
		bool operator!=(const bin_cl_itr &o) const { return !(*this == o); }
	};

public:
	/*
	 * (de-)construction
	 */

	ksat(const ksat &) = delete;
	ksat() {}
	~ksat();

	ksat & operator=(const ksat &) = delete;

	/*
	 * control
	 */

	void init(uint32_t nvars);
	void add_clause(std::vector<lit> &c);
	uint32_t add_var();

	lit next_decision() const;
	void make_decision(lit l);
	const watch * propagate_units(struct statistics *stats);
	res_info analyze(const watch *w, std::vector<lit> (&v)[2], struct statistics *stats) const;
	void learn_clause(std::vector<lit> &, uint32_t lbd, struct statistics *stats);

	/* requires: decisions.size() > dlevel */
	void trackback(uint32_t dlevel);

	void vacuum();

	status run();

	/*
	 * access to state
	 */

	bool is_unsat() const { return unsat; }
	status get_status() const;
	uint32_t num_vars() const { return nvars; }

	//unsigned get_assign(uint32_t v) const { return vars[v].have() ? 1U << vars[v].value : 0; }
	status get_assign(uint32_t v) const { return value(v); }
	status get_assign(lit l) const { return value(l); }

	const std::vector<uint32_t> & get_decisions() const { return decisions; }

	/*
	 * access clauses: iterators
	 */

	/* assignments (including reasons) */
	typename decltype(units)::const_iterator units_begin() const { return units.begin(); }
	typename decltype(units)::const_iterator units_end()   const { return units.end(); }
	size_t                                   units_size()  const { return units.size(); }

	bin_cl_itr binary_clauses_begin() const { return bin_cl_itr(*this, 0); }
	bin_cl_itr binary_clauses_end()   const { return bin_cl_itr(*this, 2*nvars); }

	/* clauses of size >= 3 */
	clause_db::iterator large_clauses_begin() const { return db.begin(); }
	clause_db::iterator large_clauses_end()   const { return db.end(); }

	typedef concat_itr<const clause,bin_cl_itr,clause_db::iterator> clause_itr;

	class cl_ref {
		const ksat &sat;
	public:
		cl_ref(const ksat &sat) : sat(sat) {}
		clause_itr begin() const;
		clause_itr end() const;
	};

	/* allows 'for (const clause &cl : sat.clauses()) {...}' */
	cl_ref clauses() const { return { *this }; }

	/*
	 * stats
	 */
	void stats(int verbosity);
};

class run_context {
	std::vector<lit> cl[2];
	std::unique_ptr<statistics> stats_ptr;
	bool do_vacuum = true;
	status r;
	luby_seq luby;
	unsigned long next_restart;
	unsigned long last_vacuum;
	timer st;
	ksat &s;

public:
	explicit run_context(ksat &s);
	~run_context();

	/* these are supposed to be called in a loop akin
	 *
	 *   while ((r = ctx.propagate()) != FALSE) {
	 *     if ((r = ctx.decide()) != TRUE)
	 *       continue;
	 *     // analyze the solution...
	 *     ctx.trackback(0);               // optional
	 *     ctx.add_clause(learned_clause); // optional
	 *   }
	 */

	status propagate();
	status decide();
	void trackback(uint32_t dlevel);
	void add_clause(std::vector<lit> &c);
	uint32_t add_var();

	void stats(int verbosity) const;
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

void dump_dimacs(const ksat &solver, FILE *f, bool complete_clauses = false);

}

#endif
