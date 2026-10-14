import itertools, random
def make(gaps,N):
    B=[0]
    while B[-1]<N: B.append(B[-1]+gaps(len(B)-1))
    res=[0]*N; k=0
    for x in range(N):
        while B[k+1]<=x: k+=1
        res[x]=x-B[k]
    return res,B
def sym(gaps,M=60,N=3000):
    res,B=make(gaps,N)
    out=[]
    for T in range(1,M):
        ok=True
        for a in range(0,N//3):
            for b in range(a+1,N//3):
                if res[a]==res[b] and res[a+T]!=res[b+T]: ok=False;break
            if not ok: break
        if ok: out.append(T)
    return out
tests={'flat3':lambda k:3,'12':lambda k:[1,2][k%2],'21':lambda k:[2,1][k%2],'123':lambda k:[1,2,3][k%3],
'1122':lambda k:[1,1,2,2][k%4],'2222then':lambda k:2 if k<5 else 3,'eventually12':lambda k:5 if k==0 else [1,2][k%2],
'squares':lambda k:2*k+1,'313':lambda k:[3,1,3][k%3], '22 4':lambda k:[2,2,4][k%3]}
for n,g in tests.items(): print(n,sym(g))

random.seed(1); bad=0; cnt=0
def predicted(gl, per, M):
    # gl: function; per: minimal period or None; flat?
    vals=[gl(k) for k in range(200)]
    if len(set(vals))==1: return list(range(1,M))
    if per is None: return []
    out=[]; 
    B=[0]
    for k in range(200): B.append(B[-1]+vals[k])
    return [B[p] for p in range(1,200) if B[p]<M and all(vals[k+p]==vals[k] for k in range(100))]
for trial in range(150):
    L=random.randint(1,4); pat=[random.randint(1,4) for _ in range(L)]
    kind=random.random()
    if kind<0.6:
        g=lambda k,p=pat:p[k%len(p)]; per=L
    else:
        pre=[random.randint(1,4) for _ in range(random.randint(1,3))]
        g=lambda k,p=pat,q=pre:q[k] if k<len(q) else p[(k-len(q))%len(p)]; per=None
        vals=[g(k) for k in range(300)]
        if any(all(vals[k+p]==vals[k] for k in range(200)) for p in range(1,20)): per=1  # actually periodic; recompute
    S=sym(g,M=40,N=1500); P=predicted(g, per, 40)
    cnt+=1
    if S!=P: bad+=1; print("MISMATCH",[g(k) for k in range(12)],S,P)
print("random",cnt,bad)
