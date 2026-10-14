from math import isqrt
def iroot(a,n):
    r=int(round(a**(1/n)))
    while r**n>a: r-=1
    while (r+1)**n<=a: r+=1
    return r
def rem(a,n): return a-iroot(a,n)**n
# T1/T2: a ~ a+D  iff floor-power + D is an n-th power; and then gap(k)<=D
bad=0
for n in (2,3,4):
  for D in range(1,400):
    for a in range(0,3000):
      k=iroot(a,n); eq = rem(a,n)==rem(a+D,n)
      h=iroot(k**n+D,n); pp = h**n==k**n+D
      if eq!=pp: bad+=1
      if eq and (k+1)**n-k**n> D: bad+=1
print("T1/T2 mismatches",bad)
# T3: n=2 pair (k,k+d): forward reencounter (k'>k) iff d>=3
bad=0
for k in range(0,200):
  for d in range(1,60):
    D=(k+d)**2-k**2
    fwd=any(isqrt(kp*kp+D)**2==kp*kp+D for kp in range(k+1,D))
    if fwd!=(d>=3): bad+=1;print(k,d,fwd)
print("T3 mismatches",bad)
