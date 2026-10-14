# tripathi_floor.py — floor(tau/2) matches positive square-diff counts for n=1..500.
from math import isqrt

def tau(n):
    c = 0
    d = 1
    while d * d <= n:
        if n % d == 0:
            c += 1 if d * d == n else 2
        d += 1
    return c

def count_pos(n):
    # positive x>y>0 with x^2-y^2=n
    c = 0
    for y in range(1, n + 1):
        x2 = y * y + n
        x = isqrt(x2)
        if x * x == x2 and x > y:
            c += 1
    return c

def predicted(n):
    if n % 2 == 1:
        return tau(n) // 2
    if n % 4 == 0:
        return tau(n // 4) // 2
    return 0

bad_floor = bad_literal = 0
for n in range(1, 501):
    actual = count_pos(n)
    if predicted(n) != actual:
        bad_floor += 1
    # literal floor((d-1)/2) display
    if n % 2 == 1:
        lit = (tau(n) - 1) // 2
    elif n % 4 == 0:
        lit = (tau(n // 4) - 1) // 2
    else:
        lit = 0
    if lit != actual:
        bad_literal += 1
print("floor_tau/2 mismatches", bad_floor)
print("literal floor((d-1)/2) mismatches", bad_literal)
raise SystemExit(0 if bad_floor == 0 else 1)
