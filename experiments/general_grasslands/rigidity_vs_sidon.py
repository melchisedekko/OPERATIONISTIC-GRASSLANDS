import random
def build(gaps,N):
    B=[0]
    while B[-1]<=N: B.append(B[-1]+gaps[len(B)-1])
    chap=[0]*(N+1);k=0
    for x in range(N+1):
        while B[k+1]<=x: k+=1
        chap[x]=k
    return B,[x-B[chap[x]] for x in range(N+1)]
random.seed(5); bad=0
for trial in range(300):
    L=8
    if trial%2: gaps=[2**i+random.randint(0,1) for i in range(L)]+[10**6]*5
    else: gaps=[random.randint(1,9) for _ in range(L)]+[10**6]*5
    B,res=build(gaps,B_:=sum(gaps[:L+1])) if False else build(gaps,sum(gaps[:L])+gaps[L]-1)
    Bs=B[:L+1]
    sidon=len({Bs[h]-Bs[k] for k in range(L+1) for h in range(k+1,L+1)})==(L+1)*L//2
    rigid=True
    for k in range(L):
        for h in range(k+1,L):
            for t in range(min(gaps[k],gaps[h])):
                for m in range(0,Bs[L]-Bs[h]-t):
                    L_=res[Bs[k]+t+m]==res[Bs[h]+t+m]; R=m<min(gaps[k],gaps[h])-t
                    if L_!=R: rigid=False
    # restricted to chapters < L (finite truncation) -- compare with Sidon of B_0..B_L
    if rigid!=sidon:
        bad+=1; print(gaps[:L], "sidon",sidon,"rigid",rigid, sorted([(Bs[h]-Bs[k],k,h) for k in range(L+1) for h in range(k+1,L+1)]))
print("mismatch",bad)
