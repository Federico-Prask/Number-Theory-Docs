#include "number_theory.hpp"
#include <boost/multiprecision/cpp_int.hpp>
#include <iostream>
#include <string>
using namespace nt;
using boost::multiprecision::cpp_int;

int main() {
    std::uint64_t checks=0;
    for (i64 a=-100;a<=100;++a) for (i64 b=1;b<=30;++b) {
        i128 f=floor_div(a,b),c=ceil_div(a,b);
        assert(f*b<=a && a<(f+1)*b);
        assert((c-1)*b<a && a<=c*b); ++checks;
    }
    for (u64 m=1;m<=120;++m) for (u64 a=0;a<=m+1;++a) {
        std::vector<i64> expected(m,-1);
        u64 v=1%m;
        for (u64 x=0;expected[v]<0;++x) {
            expected[v]=x; v=mul_mod(v,a,m);
        }
        for (u64 b=0;b<m;++b) {
            auto x=exbsgs(a,b,m);
            assert((x ? (i64)*x : -1)==expected[b]); ++checks;
            if (m==1 || std::gcd(a,m)==1) {
                auto y=bsgs(a,b,m);
                assert((y ? (i64)*y : -1)==expected[b]); ++checks;
            }
        }
        auto inv=inverse_mod(a,m);
        assert((bool)inv==(std::gcd(a,m)==1));
        if (inv) assert(mul_mod(a,*inv,m)==1%m);
        ++checks;
    }
    std::cout<<"signed division, inverse, BSGS/exBSGS passed\n";
    for (i64 m=1;m<=18;++m) for (i64 n=1;n<=18;++n)
        for (i64 a=0;a<m;++a) for (i64 b=0;b<n;++b) {
            auto ans=merge({true,a,m},b,n);
            i64 L=std::lcm(m,n),expected=-1;
            for (i64 x=0;x<L;++x) if (x%m==a && x%n==b) {
                expected=x; break;
            }
            assert(ans.ok==(expected>=0));
            if (ans.ok) assert(ans.r==expected && ans.m==L);
            ++checks;
        }
    bool overflow=false;
    try { (void)merge({true,0,4000000000LL},0,4000000001LL); }
    catch (const std::overflow_error&) { overflow=true; }
    assert(overflow);
    std::cout<<"CRT exhaustive small cases and overflow guard passed\n";
    for (u64 M=1;M<=150;++M) {
        std::vector<PrimePowerBinom> plans;
        auto fac=factor(M);
        for (std::size_t i=0;i<fac.size();) {
            std::size_t j=i; while (j<fac.size() && fac[j]==fac[i]) ++j;
            plans.emplace_back(fac[i],(unsigned)(j-i)); i=j;
        }
        for (u64 n=0;n<=80;++n) {
            cpp_int exact=1;
            for (u64 k=0;k<=n+1;++k) {
                if (k>n) exact=0;
                CRT got;
                for (const auto& pp:plans) got=merge(got,pp.choose(n,k),pp.q);
                assert(got.ok);
                u64 want=(exact%M).convert_to<u64>();
                assert((u64)got.r==want); ++checks;
                if (k<n) exact=exact*(n-k)/(k+1);
            }
        }
    }
    std::cout<<"prime-power factorial and composite binomial vs cpp_int passed\n";
    Sieve sieve(200000);
    for (u64 n=0;n<=200000;++n) {
        bool want=n>=2 && sieve.lp[n]==(int)n;
        assert(is_prime(n)==want); ++checks;
    }
    for (u64 n:{561ULL,1105ULL,1729ULL,2465ULL,2821ULL,6601ULL,
                341550071728321ULL,3825123056546413051ULL,
                18446744073709551615ULL}) {
        assert(!is_prime(n)); ++checks;
    }
    for (u64 n:{2ULL,3ULL,998244353ULL,1000000007ULL,
                18446744073709551557ULL}) { assert(is_prime(n)); ++checks; }
    for (u64 n=1;n<=10000;++n) {
        auto fac=factor(n); u128 product=1;
        for (u64 p:fac) { assert(is_prime(p)); product*=p; }
        assert(product==n); ++checks;
    }
    for (u64 n:{1000000016000000063ULL,999999874000003969ULL,
                18446744073709551615ULL,600851475143ULL}) {
        auto fac=factor(n); u128 product=1;
        for (u64 p:fac) { assert(is_prime(p)); product*=p; }
        assert(product==n); ++checks;
    }
    for (u64 m=2;m<=100;++m) {
        auto mf=factor(m); u64 ph=phi_from_factors(m,mf); auto pf=factor(ph);
        u64 direct=0;
        for (u64 a=1;a<m;++a) if (std::gcd(a,m)==1) {
            ++direct; u64 r=order(a,m,ph,pf),x=1;
            for (u64 k=1;k<=r;++k) {
                x=mul_mod(x,a,m);
                assert((x==1)==(k==r)); ++checks;
            }
        }
        assert(direct==ph);
    }
    std::cout<<"Miller-Rabin, factorization, phi and order passed\n";
    std::cout<<"ALL PASS; checks="<<checks<<"\n";
}
