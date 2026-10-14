# verify_higher_examples.py — Ramanujan t=3,4 and Euler c=1,2.
bad = 0

def ram(t):
    return (t * t + 9 * t - 1, 10 * t * t + 2,
            9 * t * t - 7 * t - 1, 12 * t * t - 4 * t + 2)

k, h, kp, hp = ram(3)
if (k, h, kp, hp) != (35, 92, 59, 98):
    bad += 1
if kp ** 3 + (h ** 3 - k ** 3) != hp ** 3:
    bad += 1
if [35 ** 3, 92 ** 3, 59 ** 3, 98 ** 3] != [42875, 778688, 205379, 941192]:
    bad += 1
if 92 ** 3 - 35 ** 3 != 735813:
    bad += 1
if 59 ** 3 - 35 ** 3 != 162504:
    bad += 1
k4, h4, kp4, hp4 = ram(4)
if (k4, h4) != (51, 162):
    bad += 1
if 35 * 162 == 92 * 51:
    bad += 1
if 35 * 162 != 5670 or 92 * 51 != 4692:
    bad += 1
if 59 ** 4 + 158 ** 4 != 133 ** 4 + 134 ** 4:
    bad += 1
if 59 ** 4 + 158 ** 4 != 635318657:
    bad += 1
if (59 * 2) ** 4 + (158 * 2) ** 4 != (133 * 2) ** 4 + (134 * 2) ** 4:
    bad += 1
print("mismatches", bad)
raise SystemExit(bad)
