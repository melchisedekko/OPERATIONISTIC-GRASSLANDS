import random
def build(gl,N):
    B=[0]
    while B[-1]<=2*N: B.append(B[-1]+gl(len(B)-1))
    chap=[0]*(2*N+1); k=0
    for x in range(2*N+1):
        while B[k+1]<=x: k+=1
        chap[x]=k
    res=[x-B[chap[x]] for x in range(2*N+1)]
    return B,chap,res
random.seed(2)
# 1. general dictionary
bad=0
for trial in range(60):
    pat=[random.randint(1,6) for _ in range(40)]
    gl=lambda k,p=pat: p[k%40]
    N=600; B,chap,res=build(gl,N); Bs=set(B)
    for a in range(N):
        for D in range(0,N):
            k=chap[a]
            L=res[a]==res[a+D]
            R=any(B[h]==B[k]+D and res[a]<gl(h) for h in range(len(B)) if B[h]==B[k]+D)
            bad+=L!=R
print("dictionary mismatches",bad)
# 3. Mersenne: gaps 2^k ; pair (B_k+t,B_h+t) equivalent only on first window
gl=lambda k:2**k; N=1<<14; B,chap,res=build(gl,N); extra=0
for k in range(0,10):
  for h in range(k+1,12):
    for t in range(0,2**k):
      for m in range(0,N-B[h]-t):
        if res[B[k]+t+m]==res[B[h]+t+m] and m>=2**k-t: extra+=1
print("mersenne extra equivalences",extra)
# 4. Fibonacci gaps F_{k+1}: 1,1,2,3,5,...  which pairs reencounter beyond first window?
F=[1,1]
for i in range(60): F.append(F[-1]+F[-2])
gl=lambda k:F[k]; N=200000; B,chap,res=build(gl,N)
from collections import defaultdict
d=defaultdict(list)
for k in range(0,22):
  for h in range(k+1,24):
    d[B[h]-B[k]].append((k,h))
multi={D:v for D,v in d.items() if len(v)>1}
print("fib multi reps sample",sorted(multi.items())[:12], len(multi))
