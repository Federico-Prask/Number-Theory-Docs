#pragma once
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <limits>
#include <numeric>
#include <optional>
#include <random>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace nt {
using i64 = std::int64_t;
using u64 = std::uint64_t;
using i128 = __int128_t;
using u128 = __uint128_t;

inline i128 norm(i128 a, i128 m) {
    assert(m > 0);
    a %= m;
    return a < 0 ? a + m : a;
}
inline i128 floor_div(i128 a, i128 b) {
    assert(b > 0);
    return a / b - (a % b < 0);
}
inline i128 ceil_div(i128 a, i128 b) {
    assert(b > 0);
    return a / b + (a % b > 0);
}
inline i128 exgcd(i128 a, i128 b, i128 &x, i128 &y) {
    assert(a >= 0 && b >= 0 && (a || b));
    if (!b) { x = 1; y = 0; return a; }
    i128 u, v;
    i128 d = exgcd(b, a % b, u, v);
    x = v; y = u - (a / b) * v;
    return d;
}

// [modular begin]
inline u64 mul_mod(u64 a, u64 b, u64 m) {
    assert(m > 0);
    return (u128)a * b % m;
}
inline u64 pow_mod(u64 a, u64 e, u64 m) {
    assert(m > 0);
    u64 r = 1 % m; a %= m;
    for (; e; e >>= 1, a = mul_mod(a, a, m))
        if (e & 1) r = mul_mod(r, a, m);
    return r;
}
inline std::optional<u64> inverse_mod(u64 a, u64 m) {
    assert(m > 0);
    // The residue for modulus 1 is returned as a programming convention.
    if (m == 1) return 0;
    i128 x, y;
    if (exgcd(a % m, m, x, y) != 1) return std::nullopt;
    return (u64)norm(x, m);
}
// [modular end]

struct CRT {
    bool ok = true;
    i64 r = 0, m = 1;
};
// Inputs and merged modulus must fit positive int64_t.
// A too-large lcm raises overflow_error, not an incorrect residue.
inline CRT merge(CRT cur, i64 b, i64 n) {
    assert(n > 0 && cur.m > 0);
    if (!cur.ok) return cur;
    i128 a = norm(cur.r, cur.m), m = cur.m;
    b = (i64)norm(b, n);
    i128 x, y, d = exgcd(m, n, x, y);
    if ((b-a) % d) return {false, 0, 1};
    i128 q = n/d, t = norm(((b-a)/d)*x, q);
    i128 L = m*q;
    if (L > std::numeric_limits<i64>::max())
        throw std::overflow_error("CRT modulus exceeds int64_t");
    return {true, (i64)norm(a+m*t,L), (i64)L};
}

// [bsgs begin]
inline std::optional<u64> bsgs(u64 a, u64 b, u64 m) {
    assert(m > 0);
    if (m == 1) return 0;
    a %= m; b %= m;
    if (std::gcd(a,m) != 1) return std::nullopt;
    if (b == 1) return 0;
    if (std::gcd(b,m) != 1) return std::nullopt;
    u64 B = (u64)std::sqrt((long double)m);
    while ((u128)B*B < m) ++B;
    while (B && (u128)(B-1)*(B-1) >= m) --B;
    // Caller is responsible for the O(sqrt(m)) memory budget.
    std::unordered_map<u64,u64> baby;
    baby.reserve((std::size_t)(B*2+1));
    u64 v = 1;
    for (u64 j=0;j<B;++j) {
        baby.emplace(v,j); // Keep the earliest/smallest j.
        v = mul_mod(v,a,m);
    }
    u64 step = *inverse_mod(v,m), giant = b;
    for (u64 i=0;i<=B;++i) {
        auto it = baby.find(giant);
        if (it != baby.end()) {
            u128 x = (u128)i*B+it->second;
            if (x < m) return (u64)x;
        }
        giant = mul_mod(giant,step,m);
    }
    return std::nullopt;
}
inline std::optional<u64> exbsgs(u64 a, u64 b, u64 m) {
    assert(m > 0);
    if (m == 1) return 0;
    a %= m; b %= m;
    if (b == 1) return 0;
    if (a == 0) return b == 0 ? std::optional<u64>(1) : std::nullopt;
    u64 count = 0, k = 1;
    while (true) {
        u64 d = std::gcd(a,m);
        if (d == 1) break;
        if (b == k) return count;
        if (b % d) return std::nullopt;
        b /= d; m /= d; ++count;
        if (m == 1) return count;
        k = mul_mod(k,a/d,m);
    }
    auto inv = inverse_mod(k,m);
    assert(inv.has_value());
    auto tail = bsgs(a,mul_mod(b,*inv,m),m);
    if (!tail) return std::nullopt;
    return *tail + count;
}
// [bsgs end]

struct Sieve {
    std::vector<int> primes, lp, phi, mu;
    explicit Sieve(int N):lp(N+1),phi(N+1),mu(N+1) {
        assert(N >= 1);
        phi[1]=mu[1]=1;
        for (int i=2;i<=N;++i) {
            if (!lp[i]) {
                lp[i]=i; primes.push_back(i);
                phi[i]=i-1; mu[i]=-1;
            }
            for (int p:primes) {
                if (p>N/i) break;
                int v=i*p; lp[v]=p;
                if (i%p==0) {
                    phi[v]=phi[i]*p; mu[v]=0; break;
                }
                phi[v]=phi[i]*(p-1); mu[v]=-mu[i];
            }
        }
    }
};

// [primepower begin]
struct PrimePowerBinom {
    u64 p, q = 1;
    unsigned alpha;
    std::vector<u64> pref;
    // Contract: p is prime. Table size must be affordable.
    PrimePowerBinom(u64 prime, unsigned exponent,
                    u64 table_limit=2000000):p(prime),alpha(exponent) {
        assert(p>=2 && alpha>=1);
        for (unsigned i=0;i<alpha;++i) {
            if (q>table_limit/p) throw std::length_error("prime-power table too large");
            q*=p;
        }
        pref.assign(q+1,1);
        for (u64 i=1;i<=q;++i)
            pref[i]=(i%p) ? mul_mod(pref[i-1],i,q) : pref[i-1];
        assert(pref[q]==1 || pref[q]==q-1);
    }
    u64 valuation(u64 n) const {
        u64 e=0;
        while (n) { n/=p; e+=n; }
        return e;
    }
    u64 unit(u64 n) const {
        u64 r=1;
        while (n) {
            r=mul_mod(r,pref[n%q],q);
            if ((n/q)&1) r=mul_mod(r,pref[q],q);
            n/=p;
        }
        return r;
    }
    u64 choose(u64 n,u64 k) const {
        if (k>n) return 0;
        u64 e=valuation(n)-valuation(k)-valuation(n-k);
        if (e>=alpha) return 0;
        u64 r=unit(n);
        r=mul_mod(r,*inverse_mod(unit(k),q),q);
        r=mul_mod(r,*inverse_mod(unit(n-k),q),q);
        return mul_mod(r,pow_mod(p,e,q),q);
    }
};
// [primepower end]

// [miller begin]
inline bool is_prime(u64 n) {
    if (n<2) return false;
    for (u64 p:{2ULL,3ULL,5ULL,7ULL,11ULL,13ULL,
                17ULL,19ULL,23ULL,29ULL,31ULL,37ULL})
        if (n%p==0) return n==p;
    u64 d=n-1; unsigned s=0;
    while (!(d&1)) { d>>=1; ++s; }
    for (u64 base:{2ULL,325ULL,9375ULL,28178ULL,
                   450775ULL,9780504ULL,1795265022ULL}) {
        u64 a=base%n;
        if (!a) continue;
        u64 x=pow_mod(a,d,n);
        if (x==1 || x==n-1) continue;
        bool pass=false;
        for (unsigned j=1;j<s;++j) {
            x=mul_mod(x,x,n);
            if (x==n-1) { pass=true; break; }
            if (x==1) break;
        }
        if (!pass) return false;
    }
    return true;
}
// [miller end]

// Not a cryptographic RNG. A fixed seed can be supplied for reproducible tests.
inline u64 rho(u64 n,std::mt19937_64 &rng) {
    assert(n>1 && !is_prime(n));
    if (n%2==0) return 2;
    if (n%3==0) return 3;
    std::uniform_int_distribution<u64> pick(1,n-1);
    constexpr int batch=64;
    while (true) {
        u64 c=pick(rng), x=pick(rng), y=x;
        auto step=[&](u64 z)->u64 {
            // The addition also needs a 128-bit intermediate.
            return ((u128)mul_mod(z,z,n)+c)%n;
        };
        bool restart=false;
        for (unsigned round=0;round<(1u<<18) && !restart;++round) {
            u64 oldx=x, oldy=y, product=1;
            for (int i=0;i<batch;++i) {
                x=step(x); y=step(step(y));
                u64 delta=x>y ? x-y : y-x;
                product=mul_mod(product,delta,n);
            }
            u64 d=std::gcd(product,n);
            if (d==1) continue;
            if (d<n) return d;
            // Recover the first useful difference in this batch.
            x=oldx; y=oldy;
            for (int i=0;i<batch;++i) {
                x=step(x); y=step(step(y));
                u64 delta=x>y ? x-y : y-x;
                d=std::gcd(delta,n);
                if (d>1 && d<n) return d;
                if (d==n) break;
            }
            restart=true;
        }
    }
}
inline void factor_rec(u64 n,std::vector<u64>& result,std::mt19937_64& rng) {
    if (n==1) return;
    if (is_prime(n)) { result.push_back(n); return; }
    u64 d=rho(n,rng);
    factor_rec(d,result,rng); factor_rec(n/d,result,rng);
}
inline std::vector<u64> factor(u64 n,u64 seed=0xBADC0FFEEULL) {
    assert(n>=1);
    std::mt19937_64 rng(seed);
    std::vector<u64> result;
    factor_rec(n,result,rng);
    std::sort(result.begin(),result.end());
    return result;
}
inline u64 phi_from_factors(u64 n,const std::vector<u64>& sorted_factors) {
    u64 r=n, prev=0;
    for (u64 p:sorted_factors) if (p!=prev) { r=r/p*(p-1); prev=p; }
    return r;
}
inline u64 order(u64 a,u64 m,u64 phi,const std::vector<u64>& phi_factors) {
    assert(m>=2 && std::gcd(a,m)==1);
    u64 r=phi, prev=0;
    for (u64 p:phi_factors) {
        if (p==prev) continue;
        while (r%p==0 && pow_mod(a,r/p,m)==1) r/=p;
        prev=p;
    }
    return r;
}
} // namespace nt
