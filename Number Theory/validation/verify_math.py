"""Independent small-case checks; not a proof of asymptotic complexity or an OJ submission."""
from functools import lru_cache
from math import gcd, isqrt, comb
from random import Random
from collections import deque
from pathlib import Path
rng=Random(20260907)
lines=[]
def report(x):
    print(x); lines.append(x)

@lru_cache(None)
def fac(n):
    r={};p=2
    while p*p<=n:
        while n%p==0: r[p]=r.get(p,0)+1;n//=p
        p+=1
    if n>1:r[n]=r.get(n,0)+1
    return r
@lru_cache(None)
def phi(n):
    r=n
    for p in fac(n):r=r//p*(p-1)
    return r
@lru_cache(None)
def mu(n):
    return 0 if any(e>1 for e in fac(n).values()) else (-1)**len(fac(n))
def vp(n,p):
    assert n
    n=abs(n);r=0
    while n%p==0:n//=p;r+=1
    return r

# Positive Diophantine intervals and the unique-y formula.
cnt=0
for a in range(1,20):
 for b in range(1,20):
  for c in range(1,80):
   d=gcd(a,b)
   solutions=[(x,y) for x in range(1,c//a+1) for y in range(1,c//b+1) if a*x+b*y==c]
   if c%d: assert not solutions;continue
   # Find any (possibly nonpositive) particular solution independently.
   x0=next(x for x in range(b//d) if (c-a*x)%b==0)
   y0=(c-a*x0)//b
   A,B=a//d,b//d
   L=-((x0-1)//B);R=(y0-1)//A
   got=[(x0+B*t,y0-A*t) for t in range(L,R+1)]
   assert got==solutions;cnt+=1
for x in range(1,101):
 for y in range(1,101):
  z=x*y*gcd(x,y);w=z//x;g=gcd(w,x*x);d=isqrt(g)
  assert d*d==g and w//d==y;cnt+=1
report(f'exgcd intervals and P8255 constructed instances: {cnt} passed')

cnt=0
for p in [2,3,5,7]:
 for x in range(1,16):
  for y in range(1,x):
   if x%p==0 or y%p==0 or (x-y)%p:continue
   for n in range(1,17):
    actual=vp(x**n-y**n,p)
    want=vp(x-y,p)+vp(n,p)
    if p==2 and n%2==0:want=vp(x-y,2)+vp(x+y,2)+vp(n,2)-1
    if p==2 and n%2:want=vp(x-y,2)
    assert actual==want;cnt+=1
report(f'LTE: {cnt} finite instances passed')

# Ragged-prefix P4240 implementation.
MOD=998244353;N=40;B=6;K=N//B
f=[0]+[mu(k)**2*pow(phi(k),-1,MOD)%MOD for k in range(1,N+1)]
G={k:[0] for k in range(1,N+1)}
for k in G:
 for t in range(1,N//k+1):G[k].append((G[k][-1]+phi(k*t))%MOD)
H={}
for u in range(1,B+1):
 for v in range(1,B+1):
  hi=N//max(u,v)
  if hi<=K:continue
  row=[0]
  for k in range(K+1,hi+1):row.append((row[-1]+f[k]*G[k][u]*G[k][v])%MOD)
  H[u,v]=row
for n in range(1,N+1):
 for m in range(1,N+1):
  ans=sum(f[k]*G[k][n//k]*G[k][m//k] for k in range(1,min(K,n,m)+1))%MOD
  l=K+1
  while l<=min(n,m):
   u,v=n//l,m//l;r=min(n//u,m//v)
   ans=(ans+H[u,v][r-K]-H[u,v][l-1-K])%MOD;l=r+1
  assert ans==sum(phi(i*j) for i in range(1,n+1) for j in range(1,m+1))%MOD
report(f'P4240 ragged tables: all {N*N} rectangles passed')

# Two-stage prime / multiplicative sieve, on all quotient values.
def prime_sieve_sum(n,kind):
 vals=sorted({n//i for i in range(1,n+1)},reverse=True)
 ps=[p for p in range(2,isqrt(n)+1) if len(fac(p))==1 and fac(p).get(p)==1]
 gs=[{v:v-1 for v in vals},{v:v*(v+1)//2-1 for v in vals},
     {v:v*(v+1)*(2*v+1)//6-1 for v in vals}]
 for t,gg in enumerate(gs):
  pref=0
  for p in ps:
   for v in vals:
    if p*p>v:break
    gg[v]-=p**t*(gg[v//p]-pref)
   pref+=p**t
 if kind=='given':pp=lambda p,e:p**e*(p**e-1);h={v:gs[2][v]-gs[1][v] for v in vals}
 elif kind=='phi':pp=lambda p,e:p**(e-1)*(p-1);h={v:gs[1][v]-gs[0][v] for v in vals}
 elif kind=='mu':pp=lambda p,e:-(e==1);h={v:-gs[0][v] for v in vals}
 else:pp=lambda p,e:e+1;h={v:2*gs[0][v] for v in vals}
 pref=[0]*(isqrt(n)+1)
 for i in range(1,len(pref)):pref[i]=pref[i-1]+(pp(i,1) if i in ps else 0)
 for p in reversed(ps):
  for v in vals:
   if p*p>v:break
   pe=p;e=1;delta=0
   while pe<=v:
    u=v//pe
    delta+=pp(p,e)*((e>=2)+h[u]-pref[min(p,u)])
    pe*=p;e+=1
   h[v]+=delta
 def direct(x):
  r=1
  for p,e in fac(x).items():r*=pp(p,e)
  return r
 for v in vals:assert h[v]+1==sum(direct(i) for i in range(1,v+1)),(n,kind,v,h[v])
for n in range(1,181):
 for kind in ['given','phi','mu','tau']:prime_sieve_sum(n,kind)
report('Two-stage sieve: 720 instances, every quotient state checked')

# Two-dimensional convolution decompositions.
for trial in range(12):
 n=18;w=[rng.randrange(5) for _ in range(3)]
 def S(x):
  r=1
  for p,e in fac(x).items():r*=w[0]+w[1]*p**e+w[2]*p**(2*e)
  return r
 pre=[0]
 for i in range(1,n+1):pre.append(pre[-1]+S(i))
 local={};local2={}
 for p in range(2,n+1):
  if fac(p)!={p:1}:continue
  E=0
  while p**(E+1)<=n:E+=1
  sp=lambda e:1 if e==0 else w[0]+w[1]*p**e+w[2]*p**(2*e)
  h={(0,0):1};hh={(0,0):1}
  for s in range(1,2*E+1):
   for a in range(E+1):
    b=s-a
    if not 0<=b<=E:continue
    h[a,b]=sp(s)-sum(sp(i)*sp(j)*h[a-i,b-j] for i in range(a+1) for j in range(b+1) if i+j)
  for s in range(1,2*E+1):
   for a in range(E+1):
    b=s-a
    if not 0<=b<=E:continue
    hh[a,b]=h[a,b]-sum(h[j,j]*hh[a-j,b-j] for j in range(1,min(a,b)+1))
    if a==0 or b==0 or a==b:assert hh[a,b]==0
  local[p]=h;local2[p]=hh
 def value(x,y,tab):
  r=1;fx,fy=fac(x),fac(y)
  for p in fx.keys()|fy.keys():r*=tab[p][fx.get(p,0),fy.get(p,0)]
  return r
 def L(A,B):return sum(value(d,d,local)*pre[A//d]*pre[B//d] for d in range(1,min(A,B)+1))
 direct=sum(S(x*y) for x in range(1,n+1) for y in range(1,n+1))
 v1=sum(value(x,y,local)*pre[n//x]*pre[n//y] for x in range(1,n+1) for y in range(1,n+1))
 v2=sum(value(x,y,local2)*L(n//x,n//y) for x in range(1,n+1) for y in range(1,n+1))
 assert direct==v1==v2,(trial,w)
report('2D axis/diagonal decompositions: 12 coefficient triples passed')

# Six-state AGC031F reduction against the full graph of (vertex,residue).
def agc_check(n,M,edges):
 adj=[[] for _ in range(n)]
 for u,v,w in edges:adj[u].append((v,w));adj[v].append((u,w))
 g=M
 for _,_,w in edges:g=gcd(g,w-edges[0][2])
 q=gcd(M,3*g);z=edges[0][2]%g
 par=list(range(6*n))
 def find(x):
  while par[x]!=x:par[x]=par[par[x]];x=par[x]
  return x
 def union(x,y):par[find(x)]=find(y)
 def ID(u,e,k):return u*6+e*3+k
 for u,v,w in edges:
  c=(w-z)//g
  for e in range(2):
   for k in range(3):
    union(ID(u,e,k),ID(v,e^1,(2*k+c)%3))
    union(ID(v,e,k),ID(u,e^1,(2*k+c)%3))
 vis=set();e,x=0,z%q
 while (e,x) not in vis:vis.add((e,x));e^=1;x=x*2%q
 for t in range(n):
  seen={(t,0)};queue=deque(seen)
  while queue:
   u,x=queue.popleft()
   for v,w in adj[u]:
    nxt=v,(2*x+w)%M
    if nxt not in seen:seen.add(nxt);queue.append(nxt)
  for s in range(n):
   for r in range(M):
    got=any(find(ID(t,0,0))==find(ID(s,e,k)) and (e,(r+z-k*g)%q) in vis for e in range(2) for k in range(3))
    assert got==((s,r) in seen),(n,M,edges,s,t,r)
for trial in range(180):
 n=rng.randrange(1,6);M=rng.randrange(1,17)*2-1
 edges=[(v,rng.randrange(v),rng.randrange(M)) for v in range(1,n)]
 for _ in range(rng.randrange(1,5)):edges.append((rng.randrange(n),rng.randrange(n),rng.randrange(M)))
 agc_check(n,M,edges)
report('AGC031F six-state reduction: 180 graphs, all endpoint/residue queries passed')

# Rook recurrence, closed formula and source examples.
R=[[0]*13 for _ in range(13)];R[0][0]=1
for n in range(1,13):
 R[n][0]=1
 for m in range(1,n+1):
  R[n][m]=R[n-1][m]+(2*n-m)*R[n-1][m-1]
  assert R[n][m]==comb(n,m)**2*__import__('math').factorial(m)
report('P7488 recurrence and closed form: n<=12 passed')

# WC2020 formula versus subset-cover enumeration.
def wc(M,vals):
 n=len(vals);cover=[]
 for a in vals:
  powers=set();x=a
  while x not in powers:powers.add(x);x=x*a%M
  cover.append(sum(1<<j for j,b in enumerate(vals) if b in powers))
 union=[0]*(1<<n)
 for mask in range(1,1<<n):
  bit=mask&-mask;union[mask]=union[mask^bit]|cover[bit.bit_length()-1]
 expected=0
 for mask in range(1,1<<n):
  best=n;s=mask
  while s:
   if mask&~union[s]==0:best=min(best,s.bit_count())
   s=(s-1)&mask
  expected+=best
 groups={};non=[]
 for i,a in enumerate(vals):
  if gcd(a,M)>1:non.append(i);continue
  x=a;order=1
  while x!=1:x=x*a%M;order+=1
  groups.setdefault(order,[]).append(i)
 ans=0
 for order,ids in groups.items():
  c=len(ids);u=sum(len(others) for d,others in groups.items() if d!=order and d%order==0)
  ans+=(2**c-1)*2**(n-c-u)
 for i in non:
  u=sum(j!=i and (cover[j]>>i)&1 for j in non)
  ans+=2**(n-1-u)
 assert ans==expected,(M,vals,ans,expected)
 return ans
assert wc(7,[1,3,4,6])==17
assert wc(9,list(range(1,9)))==532
for _ in range(60):
 M=rng.choice([7,9,13,25,27,49]);vals=rng.sample(range(1,M),min(7,M-1))
 wc(M,vals)
report('WC2020 expectation: 62 subset-enumerated cases passed, including both examples')

Path(__file__).with_name('math_test_results.txt').write_text('\n'.join(lines)+'\n')
