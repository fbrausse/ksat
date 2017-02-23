
#ifndef KSAT_HH
#define KSAT_HH

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
	} header;
	lit l[]; /* first two are watched */

	lit * begin() { return l; }
	lit * end()   { return l + header.size; }

	const lit *  begin() const { return l; }
	const lit *  end()   const { return l + header.size; }
	const lit * cbegin() const { return l; }
	const lit * cend()   const { return l + header.size; }
};

/* a clause_ptr has the same size as two literals, so in case of binary clauses,
 * which are stored solely in the watch list, use the pointer itself to store
 * the literals of the binary clause. */
union clause_proxy {
	uint32_t l[2];
	clause_ptr ptr;

	explicit operator bool() const;
};

#define LIT_SPARE_BIT		((uint32_t)1 << 31)
#define CLAUSE_PROXY_BIN_MASK	LIT_SPARE_BIT

static inline bool is_ptr(const clause_proxy &p)
{
	return !(p.l[0] & p.l[1] & CLAUSE_PROXY_BIN_MASK);
}

inline clause_proxy::operator bool() const { return !is_ptr(*this) || ptr; }

struct watch {
	clause_proxy this_cl;
	lit implied_lit;
};

struct clause_db {

	struct chunk {
		uint32_t const size;
		uint32_t valid;
		uint32_t *v;

		explicit chunk(uint32_t sz);
		chunk(const chunk &) = delete;
		chunk(chunk &&);
		~chunk();
		clause & operator[](uint32_t off) const;
		chunk & operator=(chunk) = delete;
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
	vec<chunk> chunks;

	clause_db();

	clause_ptr alloc(uint32_t size);
	clause_ptr add(uint32_t size, bool learnt);
	void       del(clause_ptr);
	clause &   operator[](clause_ptr p) const;

	iterator begin() const { return iterator(*this, {0,1}); }
	iterator end()   const { return iterator(*this, {chunks.size(),0}); }
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

	lit next_decision() const;
	uint32_t analyze(const watch *w, std::vector<lit> (&v)[2], unsigned long *, unsigned long *, unsigned long *) const;
	void add_clause0(std::vector<lit> &);
	int32_t resolve_conflict(const watch *w, std::vector<lit> (&v)[2], measurement &m) const;
	void trackback(uint32_t dlevel);

	bool add_unit(lit l, const clause_proxy &p=clause_proxy{.ptr=CLAUSE_PTR_NULL});

	void deref(const clause_proxy &p, lit *tmp, const lit **start, const lit **end) const
	{
		if (is_ptr(p)) {
			const clause &cp = db[p.ptr];
			*start = cp.begin();
			*end = cp.end();
		} else {
			tmp[0] = {p.l[0] & ~CLAUSE_PROXY_BIN_MASK};
			tmp[1] = {p.l[1] & ~CLAUSE_PROXY_BIN_MASK};
			*start = tmp;
			*end = tmp+2;
		}
	}

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

	const watch * propagate_single(lit l);
	const watch * propagate_units(unsigned long *, unsigned long *);

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
