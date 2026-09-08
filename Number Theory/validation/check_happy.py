from math import gcd
from random import Random

def side(n,m,z,initial):
 d=gcd(n,m); L=n//d; inv=pow(m//d,-1,L) if L>1 else 0
 groups={}
 for x in z:
  r=x%d; pos=((x-r)//d*inv)%L
  dic=groups.setdefault(r,{})
  dic[pos]=min(dic.get(pos,10**40),x)
 if len(groups)<d: return None
 mask={}
 for x in initial:
  r=x%d; pos=((x-r)//d*inv)%L
  mask.setdefault(r,set()).add(pos)
 ans=-1
 for r,dic in groups.items():
  a=sorted(dic); c=[dic[t]-m*t for t in a]; s=[10**40]*(len(a)+1)
  for i in range(len(a)-1,-1,-1): s[i]=min(c[i],s[i+1])
  if a[0]>0: ans=max(ans,m*(a[0]-1)+s[0]+m*L)
  pre=10**40
  for i,t in enumerate(a):
   pre=min(pre,c[i]); end=a[i+1]-1 if i+1<len(a) else L-1
   if end in mask.get(r,set()): continue
   ans=max(ans,m*end+min(pre,s[i+1]+m*L))
 return ans

def fast(n,m,b,g):
 z=b+g
 x=side(n,m,z,b); y=side(m,n,z,g)
 return -1 if x is None or y is None else max(x,y)

def brute(n,m,b,g):
 b=set(b);g=set(g)
 if len(b)==n and len(g)==m:return -1
 for t in range(n*m*(n+m+1)):
  x,y=t%n,t%m
  if x in b or y in g: b.add(x);g.add(y)
  if len(b)==n and len(g)==m:return t
 return -1
rng=Random(571)
for n in range(1,13):
 for m in range(1,13):
  for _ in range(100):
   b=[i for i in range(n) if rng.randrange(3)==0]
   g=[i for i in range(m) if rng.randrange(3)==0]
   assert fast(n,m,b,g)==brute(n,m,b,g),(n,m,b,g,fast(n,m,b,g),brute(n,m,b,g))
print('CF516E: 14400 random small cases passed; counterexample:',fast(5,3,[4],[0]))
