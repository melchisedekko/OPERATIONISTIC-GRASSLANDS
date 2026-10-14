def iroot(a,n):
    r=int(round(a**(1/n)))
    while r**n>a: r-=1
    while (r+1)**n<=a: r+=1
    return r
rem=lambda a,n:a-iroot(a,n)**n
gap=lambda n,k:(k+1)**n-k**n
bad=tot=0
for n in (2,3):
  for k in range(0,10):
    for h in range(k+1,k+7):
      D=h**n-k**n
      K=0
      while gap(n,K+1)<=D: K+=1
      top=(K+2)**n            # beyond this no equivalence (gap>D)
      for t in range(0,gap(n,k)):
        base=k**n+t
        L=sum(1 for a in range(base,top) if rem(a,n)==rem(a+D,n))
        R=(gap(n,k)-t)+sum(gap(n,kp) for kp in range(k+1,D) if iroot(kp**n+D,n)**n==kp**n+D)
        tot+=1; bad+=L!=R
        if L!=R and bad<5: print(n,k,h,t,L,R)
print(tot,bad)
