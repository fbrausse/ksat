
#ifndef KSAT_UTIL_HH
#define KSAT_UTIL_HH

#define ARRAY_SIZE(arr)		(sizeof(arr)/sizeof(*(arr)))

#ifndef CACHE_LINE_SZ
# define CACHE_LINE_SZ	64
#endif

#define NEXT_MULTIPLE(off,algn)	(((off)+(algn)-1)/(algn)*(algn))

template <typename T,size_t cache_line_sz = CACHE_LINE_SZ>
class vec {

//	static_assert(std::is_pod<T>::value, "T needs to be POD");

	static const size_t head_sz = sizeof(T*) + 2*sizeof(uint32_t);
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
	template <typename V>
	struct itr {
		V &v;
		uint32_t idx;

		itr(V &v, uint32_t idx) : v(v), idx(idx) {}

		itr & operator++()    { ++idx; return *this; }
		itr   operator++(int) { itr cpy = *this; ++*this; return cpy; }

		      T & operator* ()       { return v[idx]; }
		const T & operator* () const { return v[idx]; }
		      T * operator->()       { return &**this; }
		const T * operator->() const { return &**this; }

		bool operator==(const itr &o) const { return idx == o.idx; }
		bool operator!=(const itr &o) const { return idx != o.idx; }
	};

	static constexpr uint32_t init_cap() { return sizeof(init)/sizeof(T); }

	typedef itr<vec>       iterator;
	typedef itr<const vec> const_iterator;

	vec() : body(nullptr), sz(0), cap(init_cap()) {}
	explicit vec(size_t n) : vec() { reserve(n); }
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
			for (uint32_t i=0; i<std::min(sz,init_cap()); i++)
				new (at(i)) T(std::move(o[i]));
		o.body = nullptr;
		o.sz = 0;
	}

	vec & operator=(vec) = delete;

	void reserve(size_t n)
	{
		if (n <= init_cap())
			return;
		if (std::is_pod<T>::value)
			body = (T *)realloc(body, ((cap = n) - init_cap()) * sizeof(T));
		else {
			T *tmp = (T *)malloc(((cap = n) - init_cap()) * sizeof(T));
			std::swap(tmp, body);
			for (uint32_t i=init_cap(); i<sz; i++)
				new (at(i)) T(std::move(tmp[i-init_cap()]));
			free(tmp);
		}
	}

	T & operator[](uint32_t idx)
	{
		return *at(idx);
	}

	const T & operator[](uint32_t idx) const
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
	uint32_t size() const { return sz; }
	uint32_t capacity() const { return cap; }

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

	void pop_back()
	{
		if (--sz < init_cap() && !std::is_pod<T>::value)
			at(sz)->~T();
	}

	void clear()
	{
		if (std::is_pod<T>::value)
			sz = 0;
		else
			while (!empty())
				pop_back();
	}
};

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
	uint32_t un = 1, vn = 1;
public:
	uint32_t operator()() const { return vn; }
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

template <typename V, typename Le>
void bin_heap_sift_up(V &v, uint32_t i, Le le)
{
	while (i && !le(v[i / 2], v[i])) {
		swap(v[i / 2], v[i]);
		i = i / 2;
	}
}
#if 0
template <typename V, typename Le>
void bin_heap_insert(V &v, lit l, const Le &le)
{
	uint32_t i = v.size();
	v.push_back(l);
	bin_heap_sift_up(v, i, le);
}
#endif
template <typename V, typename Le>
static void heapify(V &v, uint32_t i, const Le& le)
{
	while (1) {
		uint32_t c0 = 2 * i + 1;
		uint32_t min = i;
		if (c0 < v.size() && !le(v[min], v[c0]))
			min = c0;
		if (c0 + 1 < v.size() && !le(v[min], v[c0 + 1]))
			min = c0 + 1;
		if (min == i)
			return;
		swap(v[i], v[min]);
		i = min;
	}
}

template <typename V, typename Le>
static void build_bin_heap(V &v, const Le &le, uint32_t s = 0)
{
	for (uint32_t i = v.size() / 2; i > s; i--)
		heapify(v, i - 1, le);
}

#endif
