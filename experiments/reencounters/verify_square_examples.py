# verify_square_examples.py — n=2 running examples from outline §04.
def iroot2(a):
    r = int(round(a ** 0.5))
    while r * r > a:
        r -= 1
    while (r + 1) * (r + 1) <= a:
        r += 1
    return r

rem = lambda a: a - iroot2(a) ** 2
gap = lambda k: 2 * k + 1

bad = 0
# Delta=15 chapters
chs15 = [k for k in range(15) if iroot2(k * k + 15) ** 2 == k * k + 15]
if chs15 != [1, 7]:
    bad += 1
# last odd
if (15 - 1) // 2 != 7:
    bad += 1
# (1,4) time at t=1
D = 16 - 1
later = [kp for kp in range(2, D) if iroot2(kp * kp + D) ** 2 == kp * kp + D]
t = 1
time = (gap(1) - t) + sum(gap(kp) for kp in later)
offs = list(range(gap(1) - t))
for kp in later:
    start = kp * kp - 1 - t
    offs += list(range(start, start + gap(kp)))
if time != 17 or offs != [0, 1] + list(range(47, 62)):
    bad += 1
# (7,8) no later; forward time 14; backward block
D = 15
later = [kp for kp in range(8, D) if iroot2(kp * kp + D) ** 2 == kp * kp + D]
if later:
    bad += 1
if gap(7) - 1 != 14:
    bad += 1
# backward from (7,8) at t=1: numbers 50,65; negative shifts land in chapter 1
back = []
for m in (-49, -48, -47):
    a, b = 50 + m, 65 + m
    if a >= 0 and rem(a) == rem(b) and iroot2(a) == 1:
        back.append(m)
if back != [-49, -48, -47]:
    bad += 1
    print("back", back)
# Delta=24 last even
if 24 // 4 - 1 != 5:
    bad += 1
# S3 square exclusion k=4
if any(iroot2(kp * kp + 9) ** 2 == kp * kp + 9 for kp in (1, 2, 3)):
    bad += 1
# k=104
if 4 * 4 + 209 != 15 * 15 or 104 * 104 + 209 != 105 * 105:
    bad += 1
print("mismatches", bad)
raise SystemExit(bad)
