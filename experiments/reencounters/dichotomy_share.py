from collections import Counter
def frac(n,X):
    c=Counter(); k=0
    pairs=0
    # all 0<=k<h with h^n-k^n<=X
    d=1
    k=0
    while (k+1)**n-k**n<=X:
        h=k+1
        while h**n-k**n<=X:
            c[h**n-k**n]+=1; h+=1
        k+=1
    pairs=sum(c.values()); rep=sum(v for v in c.values() if v>1)
    return pairs,rep,rep/pairs
for n,Xs in ((2,[10**3,10**4,10**5,10**6]),(3,[10**6,10**8,10**10,10**11]),(4,[10**9,10**12,10**14])):
    for X in Xs: print(n,X,*frac(n,X))
