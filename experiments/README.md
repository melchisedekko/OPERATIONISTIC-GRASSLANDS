# experiments/

Numerical checks run before a statement was formalised. Each script
is self-contained (Python 3, no dependencies) and prints its mismatch count; 0 is the expected output.

| script | checks | range |
|---|---|---|
| `general_grasslands/dictionary_mersenne_fibonacci.py` | general point dictionary (60 random gap sequences); Mersenne: no equivalence after the first window; Fibonacci: colliding base differences | a, Δ < 600; k < h ≤ 12; pairs ≤ 24 |
| `general_grasslands/translation_symmetries.py` | which translations T preserve the equivalence (flat, periodic, eventually periodic, unbounded) | T < 60, points < 1000 |
| `general_grasslands/rigidity_vs_sidon.py` | rigid ⇔ Sidon bases (300 random sequences; 2 reported mismatches are truncation artefacts at the last base) | 8 chapters |
| `reencounters/dictionary_and_n2.py` | radical point dictionary; n = 2 forward reencounter iff h − k ≥ 3 | n ≤ 4, Δ < 400; k < 200 |
| `reencounters/reencounter_time.py` | exact total reencounter time (6600 cases) | n = 2, 3; k < 10 |
| `reencounters/dichotomy_share.py` | share of chapter pairs sharing their distance, n = 2, 3, 4: enumerate 0≤k<h with hⁿ−kⁿ≤X, bucket by distance | X up to 10¹¹ (n = 3), 10¹⁴ (n = 4) |
| `reencounters/verify_time_examples.py` | outline §03 running examples (times 13, 14, 10, 740) | n = 2, 3; named pairs |
| `reencounters/verify_square_examples.py` | outline §04 square examples (15, 24, S3 checks); backward offsets −49,−48,−47 for (7,8) at t=1 | n = 2 |
| `reencounters/verify_higher_examples.py` | Ramanujan t = 3, 4 and Euler c = 1, 2 | n = 3, 4 |
| `reencounters/tripathi_floor.py` | ⌊τ/2⌋ vs positive square-diff counts (Hasler / OEIS A100073) | n = 1..500 |
| `reencounters/sq_proportions.py` | forward G/A and shared-distance S/A for n = 2 from the slice A(X)=Σ_d (⌊(⌊X/d⌋−d)/2⌋+1); S counts pairs whose distance has ≥2 equal-parity factorisations | X up to 10¹² (S/A to 10⁶) |
