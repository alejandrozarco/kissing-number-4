"""Independent exact check of a 4D kissing certificate written by round_k4.py (copy of ../kissing3/check_cert_k3.py with
the Legendre kernels of S^3: Q3 (k+1) = ((2k+1)(t-uv) Q3 k - k (1-u^2)(1-v^2) Q3 (k-1)) / (k+1); n = 25).

usage: python3 check_cert_k4.py cert_D14.json

Shares no code with round_k3.py, round_k4.py or polyk.py. It uses the definitions of lean/Kissing4/Kernel.lean, except
that its kernel is the unscaled Legendre one (Lean's `Q4 k` is k! times the Q3 k here; the Lean emitter stores F_k/k!
accordingly):
  Q3 0 = 1, Q3 1 = t - uv, Q3 (k+1) = ((2k+1)(t-uv) Q3 k - k (1-u^2)(1-v^2) Q3 (k-1)) / (k+1);
  Y3 m k u v t [a][b] = u^a v^b Q3 k u v t;
  S3 m k u v t = 1/6 (Y3 uvt + Y3 utv + Y3 vut + Y3 vtu + Y3 tuv + Y3 tvu);
  Rk n m k u v t = (n-2) S3 uvt + (S3 uu1 + S3 vv1 + S3 tt1) + 1/(n-1) S3 111;
and checks
  (1) the identity  -sum_k <F_k, Rk n k u v t> - e/C(n,2) = sum_r g_r(u,v,t) z_r^T B_r z_r  by exact evaluation on
      a (D+1)^3 grid of distinct rationals (both sides have degree <= D in each variable, so agreement on the grid
      is agreement as polynomials);
  (2) every F_k and B_r symmetric and positive definite (Sylvester: all leading principal minors > 0, by
      python-flint exact determinants);
  (3) e > 0 and each multiplier g_r >= 0 on {GramOK, u, v, t <= 1/2} (by the case analysis printed below);
  (4) a float sanity check that the claimed inequality holds on random points of the region.
"""
import json, sys, itertools, random
from fractions import Fraction as Fr
from math import comb
import flint
from flint import fmpq, fmpq_mat


def Q3(k, u, v, t):  # Legendre kernels of S^3 (dimension 4)
    q0, q1 = fmpq(1), t - u * v
    if k == 0:
        return q0
    for j in range(1, k):
        q0, q1 = q1, (fmpq(2 * j + 1) * (t - u * v) * q1 - fmpq(j) * (1 - u * u) * (1 - v * v) * q0) / fmpq(j + 1)
    return q1


def Y3(m, k, u, v, t):
    q = Q3(k, u, v, t)
    return fmpq_mat(m, m, [u ** a * v ** b * q for a in range(m) for b in range(m)])


def S3(m, k, u, v, t):
    Y = (Y3(m, k, u, v, t) + Y3(m, k, u, t, v) + Y3(m, k, v, u, t) + Y3(m, k, v, t, u) + Y3(m, k, t, u, v)
         + Y3(m, k, t, v, u))
    return Y * fmpq(1, 6)


def Rk(n, m, k, u, v, t):
    one = fmpq(1)
    return (S3(m, k, u, v, t) * fmpq(n - 2) + (S3(m, k, u, u, one) + S3(m, k, v, v, one) + S3(m, k, t, t, one))
            + S3(m, k, one, one, one) * fmpq(1, n - 1))


def matDot(A, B):
    return sum((A[i, j] * B[i, j] for i in range(A.nrows()) for j in range(A.ncols())), fmpq(0))


def mult(name, u, v, t):
    x = {"u": u, "v": v, "t": t}
    h = fmpq(1, 2)
    if name == "1":
        return fmpq(1)
    if name == "detG":
        return 1 + 2 * u * v * t - u * u - v * v - t * t
    for X in "uvt":
        if name == f"1+{X}":
            return 1 + x[X]
        if name == f"1/2-{X}":
            return h - x[X]
        if name == f"(1+{X})(1/2-{X})":
            return (1 + x[X]) * (h - x[X])
    raise ValueError(name)


def q(s):
    f = Fr(s)
    return fmpq(f.numerator, f.denominator)


DEG_G = {"1": 0, "detG": 3}
for _X in "uvt":
    DEG_G.update({f"1+{_X}": 1, f"1/2-{_X}": 1, f"(1+{_X})(1/2-{_X})": 2})


def fail(msg):
    raise SystemExit(f"CERTIFICATE REJECTED: {msg}")


def main(path):
    J = json.load(open(path))
    # input validation (explicit checks, not assert, so that they also run under python -O)
    if not (isinstance(J.get("n"), int) and J["n"] == 25 and J.get("dim") == 4):
        fail("n must be the integer 25 and dim must be 4")
    n = J["n"]
    if q(J.get("cut", "0")) != fmpq(1, 2):
        fail("cut must be 1/2")
    e = q(J["e"])
    if not e > 0:
        fail("e must be positive")
    if not (isinstance(J.get("F"), list) and J["F"]):
        fail("F must be a non-empty list of blocks")
    for k, Fk in enumerate(J["F"]):
        if not (isinstance(Fk, list) and Fk and all(isinstance(r, list) and len(r) == len(Fk) for r in Fk)):
            fail(f"F{k} is not a non-empty square matrix")
    if not isinstance(J.get("SOS"), list):
        fail("SOS must be a list")
    for r, b in enumerate(J["SOS"]):
        if b.get("g") not in DEG_G:
            fail(f"SOS block {r}: unknown multiplier {b.get('g')!r}")
        Z = b.get("basis")
        if not (isinstance(Z, list) and Z and all(isinstance(z, list) and len(z) == 3 and
                                                   all(isinstance(c, int) and c >= 0 for c in z) for z in Z)):
            fail(f"SOS block {r}: basis must be a non-empty list of exponent triples of non-negative integers")
        if len({tuple(z) for z in Z}) != len(Z):
            fail(f"SOS block {r}: repeated basis monomials")
        B = b.get("B")
        if not (isinstance(B, list) and len(B) == len(Z) and all(isinstance(x, list) and len(x) == len(Z) for x in B)):
            fail(f"SOS block {r}: B must be a square matrix of the basis size")
    F = [fmpq_mat(len(Fk), len(Fk), [q(x) for row in Fk for x in row]) for Fk in J["F"]]
    S = [(b["g"], [tuple(z) for z in b["basis"]],
          fmpq_mat(len(b["B"]), len(b["B"]), [q(x) for row in b["B"] for x in row])) for b in J["SOS"]]
    # degree bound derived from the data (the field "D" of the file is not trusted): u^a v^b Q_k has total degree
    # a + b + 2k with a, b < m_k, and the substitutions in Rk do not raise it; g z^T B z has deg g + 2 max |z|.
    D = max([2 * (Fk.nrows() - 1) + 2 * k for k, Fk in enumerate(F)] +
            [DEG_G[g] + 2 * max(sum(z) for z in Z) for g, Z, _ in S])
    print(f"degree bound from the data: {D} (file says {J.get('D')!r}, not used)")
    # (3) the margin and the multipliers
    names = sorted({g for g, _, _ in S})
    print(f"n = {n}, e = {e} > 0, F-block sizes {[Fk.nrows() for Fk in F]}, SOS blocks "
          f"{[(g, B.nrows()) for g, _, B in S]}")
    print("multipliers >= 0 on {GramOK, u,v,t <= 1/2}: 1; 1+x (x >= -1 from x^2 <= 1); 1/2-x (cut); their product;"
          f" detG (GramOK). Names used: {names}")
    # (2) positive definiteness via leading principal minors
    for nm, M in [(f"F{k}", Fk) for k, Fk in enumerate(F)] + [(f"B{r}:{g}", B) for r, (g, _, B) in enumerate(S)]:
        if M != M.transpose():
            fail(f"{nm} not symmetric")
        minors = [fmpq_mat(i, i, [M[a, b] for a in range(i) for b in range(i)]).det() for i in range(1, M.nrows() + 1)]
        if not all(d > 0 for d in minors):
            fail(f"{nm} not positive definite")
    print("all blocks symmetric and positive definite (Sylvester)")
    # (1) the identity on a (D+1)^3 grid: both sides have degree <= D in each variable
    pts = [fmpq(2 * i - D, 2 * D + 1) for i in range(D + 1)]   # D+1 distinct rationals in (-1, 1)
    C2 = fmpq(comb(n, 2))
    cnt = 0
    for u, v, t in itertools.product(pts, repeat=3):
        lhs = -sum((matDot(F[k], Rk(n, F[k].nrows(), k, u, v, t)) for k in range(len(F))), fmpq(0)) - e / C2
        rhs = fmpq(0)
        for g, Z, B in S:
            z = fmpq_mat(len(Z), 1, [u ** a * v ** b * t ** c for (a, b, c) in Z])
            rhs += mult(g, u, v, t) * (z.transpose() * B * z)[0, 0]
        if lhs != rhs:
            fail(f"identity fails at {(u, v, t)}")
        cnt += 1
    print(f"identity holds exactly at all {cnt} grid points = {D + 1}^3, so it holds identically")
    # (4) float sanity on the region
    rng = random.Random(1)
    worst, k = -1e9, 0
    while k < 3000:
        u, v, t = (rng.uniform(-1, 0.5) for _ in range(3))
        if 1 + 2 * u * v * t - u * u - v * v - t * t < 0:
            continue
        k += 1
        U, V, T = (fmpq(Fr(x).limit_denominator(10 ** 6).numerator, Fr(x).limit_denominator(10 ** 6).denominator)
                   for x in (u, v, t))
        val = sum((matDot(F[j], Rk(n, F[j].nrows(), j, U, V, T)) for j in range(len(F))), fmpq(0))
        worst = max(worst, float(val.p) / float(val.q))
    if not worst <= -float(e.p) / float(e.q) / comb(n, 2) + 1e-12:
        fail(f"float sanity: sampled maximum {worst:.6g} violates the claimed bound")
    print(f"float sanity: max of sum_k <F_k, Rk> over 3000 random region points = {worst:.6g} "
          f"<= -e/C(n,2) = {-float(e.p) / float(e.q) / comb(n, 2):.6g}")
    print("CERTIFICATE OK")


if __name__ == "__main__":
    main(sys.argv[1])
