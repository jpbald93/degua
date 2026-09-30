#!/usr/bin/env python3
"""Numeric sanity checks for the De Gua formalisation (numpy only).

1. n = 3: tetrahedron with orthogonal edges at O (random rotation + offset), cross-product areas.
2. general n: Gram-determinant (n-1)-volumes, opposite facet vs sum of the n facets through O.
3. Gram det of (v_{j+1} - v_0) equals sum_i prod_{k != i} |v_k|^2.
4. Cauchy-Binet projection form: det(V V^T) = sum over k-subsets of squared k x k minors.
"""
import itertools, math
import numpy as np

rng = np.random.default_rng(20260930)

def rand_orth(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)))
    return q * np.sign(np.diag(r))

def vol_sq(pts):
    """Squared k-volume of the k-simplex with vertices pts[0..k] (Gram det / (k!)^2)."""
    x0 = pts[0]
    E = np.array([p - x0 for p in pts[1:]])
    k = len(E)
    return np.linalg.det(E @ E.T) / math.factorial(k) ** 2 if k else 1.0

def tri_area_sq(X, Y, Z):
    w = np.cross(Y - X, Z - X)
    return w @ w / 4

worst = 0.0
# 1. n = 3 cross-product version
for _ in range(1000):
    Q = rand_orth(3); O = rng.normal(size=3); a = rng.uniform(0.1, 5, 3)
    A, B, C = (O + a[i] * Q[:, i] for i in range(3))
    lhs = tri_area_sq(A, B, C)
    rhs = tri_area_sq(O, A, B) + tri_area_sq(O, B, C) + tri_area_sq(O, C, A)
    worst = max(worst, abs(lhs - rhs) / max(1, abs(lhs)))
    worst = max(worst, abs(tri_area_sq(A, B, C) - vol_sq([A, B, C])) / max(1, lhs))
print(f"[1] n=3 cross-product De Gua + cross/Gram agreement: max rel err {worst:.2e}")

# 2./3. general n, ambient dimension N >= n
worst2 = worst3 = 0.0
for n in range(1, 8):
    for _ in range(200):
        N = n + int(rng.integers(0, 3))
        Q = rand_orth(N); O = rng.normal(size=N); a = rng.uniform(0.2, 3, n)
        P = [O + a[i] * Q[:, i] for i in range(n)]
        lhs = vol_sq(P)
        rhs = sum(vol_sq([O] + P[:i] + P[i + 1:]) for i in range(n))
        worst2 = max(worst2, abs(lhs - rhs) / max(1e-300, abs(lhs)))
        v = [p - O for p in P]
        E = np.array([v[j] - v[0] for j in range(1, n)]).reshape(n - 1, N)
        g = np.linalg.det(E @ E.T) if n > 1 else 1.0
        s = sum(np.prod([a[k] ** 2 for k in range(n) if k != i]) for i in range(n))
        worst3 = max(worst3, abs(g - s) / s)
print(f"[2] general-n De Gua (n=1..7): max rel err {worst2:.2e}")
print(f"[3] Gram det = sum_i prod_(k!=i) a_k^2: max rel err {worst3:.2e}")

# 4. Cauchy-Binet projection form
worst4 = 0.0
for _ in range(300):
    N = int(rng.integers(1, 7)); k = int(rng.integers(0, N + 2))
    V = rng.normal(size=(k, N))
    lhs = np.linalg.det(V @ V.T) if k else 1.0
    rhs = sum(np.linalg.det(V[:, list(s)]) ** 2 if k else 1.0
              for s in itertools.combinations(range(N), k))
    worst4 = max(worst4, abs(lhs - rhs) / max(1, abs(lhs)))
print(f"[4] Cauchy-Binet projection form (incl. k > N, k = 0): max rel err {worst4:.2e}")

ok = max(worst, worst2, worst3, worst4) < 1e-8
print("ALL OK" if ok else "FAILURE")
raise SystemExit(0 if ok else 1)
