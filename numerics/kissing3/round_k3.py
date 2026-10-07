"""Exact rounding of the kissing fixed-n = 13 interior solution (k3.py mode mu) to a rational certificate.

usage: python3 round_k3.py sol/fixn_D10_n13_mu0.5.npz cert_D10.json [KBITS] [E]

The claim certified (H = 0, upstream `three_point_bound` with the upper cut u, v, t <= 1/2):
    P(u,v,t) := -R(u,v,t) - e / C(n,2) = sum_r g_r(u,v,t) * z_r^T B_r z_r        (polynomial identity)
    R = (n-2) s(u,v,t) + s(u,u,1) + s(v,v,1) + s(t,t,1) + s(1,1,1)/(n-1),
    s = sum_k <F_k, S_k>,  S_k[a,b] = sym. average over the 6 permutations of (u,v,t) of u^a v^b Q_k(u,v,t),
with every F_k and B_r positive definite and every g_r >= 0 on {GramOK, u,v,t <= 1/2}.

Procedure (Peyrl-Parrilo, as numerics/cells/round_cell.py in the Thomson log project, but self-contained):
  1. F_k := dyadic(X_k + mu I, 2^-KBITS), B_r := dyadic(X_r + mu I, 2^-KBITS); e := E (default 1/32, below the
     float e = 0.0353), so the dropped part of e only adds to the constant term.
  2. exact P and exact residual res = P - sum_r g_r z^T B_r z (all in Q[u,v,t], own exact arithmetic,
     independent of polyk.py);
  3. absorb res into B_0 (g = 1, z = all monomials of degree <= D/2): each monomial m goes to ONE entry
     (diagonal if m = 2 z_i, else the symmetric pair (i,j),(j,i) with half each), which keeps all data dyadic
     except for the 1/12 and 1/78 coming from n;
  4. verify exactly: the identity coefficient by coefficient, and every block positive definite (LDL^T with
     positive pivots). Write JSON (all rationals as strings).
"""
import itertools, json, os, sys, time
from fractions import Fraction as Fr
from math import comb, lcm
import numpy as np

T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:6.1f}s]", *a, flush=True)


# ------------------------------------------------------------------ exact polynomials in (u,v,t)
def padd(p, q, c=1):
    r = dict(p)
    for m, v in q.items():
        r[m] = r.get(m, 0) + c * v
        if r[m] == 0:
            del r[m]
    return r


def pmul(p, q):
    r = {}
    for m1, v1 in p.items():
        for m2, v2 in q.items():
            m = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
            r[m] = r.get(m, 0) + v1 * v2
    return {m: v for m, v in r.items() if v != 0}


def pscale(p, c):
    return {m: c * v for m, v in p.items() if c * v != 0}


ONE = {(0, 0, 0): Fr(1)}
U = {(1, 0, 0): Fr(1)}
V = {(0, 1, 0): Fr(1)}
T = {(0, 0, 1): Fr(1)}


def ppow(p, k):
    r = ONE
    for _ in range(k):
        r = pmul(r, p)
    return r


def Qs(kmax):
    """Q_0 = 1, Q_1 = t - uv, Q_{k+2} = 2 (t - uv) Q_{k+1} - (1-u^2)(1-v^2) Q_k (upstream ThreePoint.Q3)."""
    w = padd(T, pmul(U, V), -1)
    g = pmul(padd(ONE, pmul(U, U), -1), padd(ONE, pmul(V, V), -1))
    Q = [ONE, w]
    while len(Q) <= kmax:
        Q.append(padd(pscale(pmul(w, Q[-1]), 2), pmul(g, Q[-2]), -1))
    return Q


def sym6(p):
    """average of p over the 6 permutations of the variables."""
    r = {}
    for perm in itertools.permutations(range(3)):
        for m, v in p.items():
            mm = [0, 0, 0]
            for i in range(3):
                mm[perm[i]] = m[i]
            mm = tuple(mm)
            r[mm] = r.get(mm, 0) + v
    return {m: v / 6 for m, v in r.items() if v != 0}


def sub_xx1(p, var):
    """p(x, x, 1) written in the variable `var` (0, 1, 2 = u, v, t)."""
    r = {}
    for m, v in p.items():
        mm = [0, 0, 0]
        mm[var] = m[0] + m[1]
        mm = tuple(mm)
        r[mm] = r.get(mm, 0) + v
    return {m: v for m, v in r.items() if v != 0}


def monos_upto(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]


def gram_poly(B, Z):
    r = {}
    for i, zi in enumerate(Z):
        for j, zj in enumerate(Z):
            if B[i][j] != 0:
                m = (zi[0] + zj[0], zi[1] + zj[1], zi[2] + zj[2])
                r[m] = r.get(m, 0) + B[i][j]
    return {m: v for m, v in r.items() if v != 0}


# ------------------------------------------------------------------ the certificate shape
CUT = Fr(1, 2)


def multipliers(D):
    """(name, g, basis degree) in the order of k3.py Prob.tri_nonneg (blocks T_B0 .. T_B10)."""
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    out = [("1", ONE, d5)]
    for nm, X in (("u", U), ("v", V), ("t", T)):
        out.append((f"1+{nm}", padd(ONE, X), d4))
        out.append((f"1/2-{nm}", padd(pscale(ONE, CUT), X, -1), d4))
        out.append((f"(1+{nm})(1/2-{nm})", pmul(padd(ONE, X), padd(pscale(ONE, CUT), X, -1)), d4))
    detG = padd(padd(ONE, pscale(pmul(pmul(U, V), T), 2)), padd(padd(pmul(U, U), pmul(V, V)), pmul(T, T)), -1)
    out.append(("detG", detG, d3))
    return out


def s_poly(F, D):
    """s = sum_k <F_k, S_k>,  F_k of size D/2+1-k."""
    Q = Qs(D // 2)
    s = {}
    for k, Fk in enumerate(F):
        m = len(Fk)
        acc = {}
        for a in range(m):
            for b in range(m):
                if Fk[a][b] != 0:
                    acc = padd(acc, pmul(pmul(ppow(U, a), ppow(V, b)), Q[k]), Fk[a][b])
        s = padd(s, sym6(acc))
    return s


def target_poly(F, n, e, D):
    """P = -R - e/C(n,2)."""
    s = s_poly(F, D)
    s111 = sum(s.values(), Fr(0))
    R = pscale(s, Fr(n - 2))
    for var in range(3):
        R = padd(R, sub_xx1(s, var))
    R = padd(R, {(0, 0, 0): s111 / (n - 1)})
    return padd(pscale(R, -1), {(0, 0, 0): -Fr(e) / comb(n, 2)})


# ------------------------------------------------------------------ exact positive definiteness
def ldl_pd(B):
    """exact LDL^T; returns (True, min pivot) if positive definite, (False, index) otherwise."""
    n = len(B)
    A = [[Fr(x) for x in row] for row in B]
    piv = []
    for j in range(n):
        d = A[j][j]
        if d <= 0:
            return False, j
        piv.append(d)
        Aj = A[j]
        for i in range(j + 1, n):
            if A[i][j] != 0:
                f = A[i][j] / d
                Ai = A[i]
                for k in range(j + 1, n):
                    if Aj[k] != 0:
                        Ai[k] -= f * Aj[k]
    return True, min(piv)


def dyadic(x, K):
    return Fr(int(round(float(x) * 2 ** K)), 2 ** K)


def dymat(M, K):
    M = (np.asarray(M, float) + np.asarray(M, float).T) / 2
    return [[dyadic(M[i, j], K) for j in range(M.shape[0])] for i in range(M.shape[0])]


def main(solfile, out, K=40, E=Fr(1, 32)):
    sol = np.load(solfile)
    meta = json.loads(str(sol["meta"]))
    D, n = meta["D"], int(round(meta["n"]))
    assert meta["mode"] == "mu" and meta["delsarte"] is None and float(meta["n"]) == n
    mu = float(meta["mu"])
    assert 0 < E <= Fr(meta["e"]), (E, meta["e"])
    log(f"{solfile}: D={D} n={n} mu={mu:.3g} float e={meta['e']:.6g} -> exact e={E}, KBITS={K}")
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    F = [dymat(sol[f"F{k}"] + mu * np.eye(m), K) for k, m in enumerate(sizes)]
    P = target_poly(F, n, E, D)
    log(f"exact target P: {len(P)} monomials, degree {max(sum(m) for m in P)}")
    mult = multipliers(D)
    Bs, Zs = [], []
    rhs = {}
    for r, (nm, g, d) in enumerate(mult):
        X = sol[f"T_B{r}"]
        Z = monos_upto(d)
        assert X.shape == (len(Z), len(Z)), (r, X.shape, len(Z))
        B = dymat(X + mu * np.eye(len(Z)), K)
        Bs.append(B); Zs.append(Z)
        rhs = padd(rhs, pmul(g, gram_poly(B, Z)))
    res = padd(P, rhs, -1)
    rmax = max((abs(float(v)) for m, v in res.items() if m != (0, 0, 0)), default=0.0)
    r0 = float(res.get((0, 0, 0), 0))
    e_drop = (float(meta["e"]) - float(E)) / comb(n, 2)
    log(f"rounding residual: {len(res)} monomials, max |non-constant coef| {rmax:.3g}; constant {r0:.6g} "
        f"(expected about the dropped e/C(n,2) = {e_drop:.6g})")
    if not (rmax < 1e-2 * mu and abs(r0 - e_drop) < 1e-2 * mu):
        log("WARNING: residual not small against mu; positive definiteness may fail")
    # absorb into B_0
    Z0 = Zs[0]
    idx = {z: i for i, z in enumerate(Z0)}
    B0 = Bs[0]
    for m, v in res.items():
        half = tuple(x // 2 for x in m)
        if all(x % 2 == 0 for x in m) and half in idx:
            i = idx[half]; B0[i][i] += v
            continue
        for zi in Z0:
            zj = (m[0] - zi[0], m[1] - zi[1], m[2] - zi[2])
            if min(zj) >= 0 and zj in idx and zj != zi:
                i, j = idx[zi], idx[zj]
                B0[i][j] += v / 2; B0[j][i] += v / 2
                break
        else:
            raise AssertionError(f"monomial {m} not representable")
    # exact verification
    rhs = {}
    for (nm, g, d), B, Z in zip(mult, Bs, Zs):
        rhs = padd(rhs, pmul(g, gram_poly(B, Z)))
    assert padd(P, rhs, -1) == {}, "identity fails"
    log("identity P == sum_r g_r z^T B_r z holds exactly")
    for nmb, M in [(f"F{k}", Fk) for k, Fk in enumerate(F)] + [(f"B{r}:{mult[r][0]}", B) for r, B in enumerate(Bs)]:
        assert all(M[i][j] == M[j][i] for i in range(len(M)) for j in range(len(M))), nmb
        ok, mp = ldl_pd(M)
        assert ok, f"{nmb} not positive definite (pivot {mp})"
        log(f"{nmb:>22s}: size {len(M):3d}, positive definite, min pivot {float(mp):.3g}")
    dens = [x.denominator for M in F + Bs for row in M for x in row] + [Fr(E).denominator]
    Lam = lcm(*dens)
    nums = [abs(x.numerator) * (Lam // x.denominator) for M in F + Bs for row in M for x in row]
    J = {
        "claim": "for all (u,v,t) with GramOK and u,v,t <= 1/2:  sum_k <F_k, Rk n k u v t> <= -e / C(n,2)",
        "n": n, "D": D, "cut": str(CUT), "e": str(E),
        "F": [[[str(x) for x in row] for row in Fk] for Fk in F],
        "SOS": [{"g": nm, "deg": d, "basis": [list(z) for z in Z], "B": [[str(x) for x in row] for row in B]}
                for (nm, g, d), B, Z in zip(mult, Bs, Zs)],
        "Lam": str(Lam),
        "stats": {"KBITS": K, "residual_max_abs": rmax, "Lam_bits": Lam.bit_length(),
                  "max_scaled_entry_bits": max(nums).bit_length()},
        "generated_from": os.path.basename(solfile),
    }
    with open(out, "w") as fh:
        json.dump(J, fh)
    log(f"wrote {out} ({os.path.getsize(out) // 1024} KiB); Lam = 2^? : {Lam.bit_length()} bits, "
        f"max |entry|*Lam: {max(nums).bit_length()} bits")


if __name__ == "__main__":
    a = sys.argv
    main(a[1], a[2], int(a[3]) if len(a) > 3 else 40, Fr(a[4]) if len(a) > 4 else Fr(1, 32))
