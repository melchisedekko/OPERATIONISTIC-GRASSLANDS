# sq_proportions.py — forward G/A and shared-distance S/A for n=2 (article 1, Q2).
# Prints A(X), G/A, S/A (S only for X<=10^6) and B/A vs 3/log X.
from collections import Counter
import math

def AG(X):
    m = int(X ** 0.5)
    A = B = 0
    for d in range(1, m + 1):
        nk = (X // d - d) // 2 + 1
        if nk <= 0:
            continue
        A += nk
        if d <= 2:
            B += nk
    return A, A - B, B

def S_pairs(X):
    c = Counter()
    k = 0
    while True:
        d = 1
        advanced = False
        while d * d <= X:
            Delta = d * (2 * k + d)
            if Delta > X:
                break
            advanced = True
            c[Delta] += 1
            d += 1
        if not advanced and k > 0:
            break
        k += 1
        if 2 * k + 1 > X and k * k > X:
            break
    return sum(v for v in c.values() if v > 1)

print("X A G/A S/A B/A 3/lnX")
for X in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
    A, G, B = AG(X)
    S = S_pairs(X)
    print(X, A, f"{G/A:.6f}", f"{S/A:.6f}", f"{B/A:.6f}", f"{3/math.log(X):.6f}")
for X in (10 ** 9, 10 ** 12):
    A, G, B = AG(X)
    print(X, A, f"{G/A:.6f}", "-", f"{B/A:.6f}", f"{3/math.log(X):.6f}")
