# verify_time_examples.py — exact reencounter times for the article 1 running examples.
# Header: recomputes outline §03 examples; exit 0 iff all match.
from math import isqrt

def iroot(a, n):
    if a == 0:
        return 0
    r = int(round(a ** (1 / n)))
    while r ** n > a:
        r -= 1
    while (r + 1) ** n <= a:
        r += 1
    return r

rem = lambda a, n: a - iroot(a, n) ** n
gap = lambda n, k: (k + 1) ** n - k ** n

def formula(n, k, h, t):
    D = h ** n - k ** n
    later = [kp for kp in range(k + 1, D)
             if iroot(kp ** n + D, n) ** n == kp ** n + D]
    return (gap(n, k) - t) + sum(gap(n, kp) for kp in later), later

def check_blocks(n, k, h, t, later):
    bad = 0
    offs = list(range(gap(n, k) - t))
    for kp in later:
        start = kp ** n - k ** n - t
        offs += list(range(start, start + gap(n, kp)))
    for m in offs:
        if rem(k ** n + t + m, n) != rem(h ** n + t + m, n):
            bad += 1
    # spot-check non-meeting chapters
    D = h ** n - k ** n
    for kp in range(min(D, 80)):
        if kp == k or kp in later:
            continue
        for i in (0, gap(n, kp) // 2, gap(n, kp) - 1):
            m = kp ** n - k ** n - t + i
            if m < 0:
                continue
            if rem(k ** n + t + m, n) == rem(h ** n + t + m, n):
                bad += 1
    # full scan for n = 2
    if n == 2:
        full = sum(1 for m in range(D ** n)
                   if rem(k ** n + t + m, n) == rem(h ** n + t + m, n))
        if full != len(offs):
            bad += 1
    return bad, len(offs)

cases = [
    (2, 1, 5, 1, 13, [5]),
    (2, 1, 5, 0, 14, [5]),
    (2, 5, 7, 1, 10, []),
    (3, 2, 9, 0, 740, [15]),
]
total_bad = 0
for n, k, h, t, expect, expect_later in cases:
    f, later = formula(n, k, h, t)
    bad, n_offs = check_blocks(n, k, h, t, later)
    ok = (f == expect == n_offs) and later == expect_later and bad == 0
    print(n, k, h, t, "formula", f, "offs", n_offs, "later", later, "OK" if ok else "FAIL")
    if not ok:
        total_bad += 1
print("mismatches", total_bad)
raise SystemExit(total_bad)
