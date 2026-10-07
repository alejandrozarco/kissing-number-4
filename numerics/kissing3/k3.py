"""Kissing number in dimension 3: three-point SDP feasibility probe (floating point, Clarabel via cvxpy).

Domain: Delta = {(u,v,t) in [-1, 1/2]^3 : 1 + 2uvt - u^2 - v^2 - t^2 >= 0}  (inner products of 3 distinct
points of a kissing configuration).  s(u,v,t) = sum_k <F_k, S_k(u,v,t)>, F_k PSD of size D/2+1-k (k = 0..D/2),
S_k = upstream ThreePoint.S3 (symmetrised u^a v^b Q_k); total degree D.  "nonneg on Delta" is imposed by a
Putinar SOS identity with multipliers 1, 1+x, 1/2-x, (1+x)(1/2-x) (x = u,v,t) and the Gram determinant.

modes
  bv  D [D2]      classical Bachoc-Vallentin bound (N-free):  min 1 + f(1) + s(1,1,1)  s.t.
                  s <= 0 on Delta,  f(x) + 3 s(x,x,1) <= -1 on [-1,1/2],  f = sum_{j<=D2} a_j P_j, a >= 0.
                  D2 = 0 or "lp" variants: env F3=0 drops the three-point part (Delsarte LP only).
  fixn D NU       fixed-n form of upstream three_point_bound(_cut) with n = NU (real allowed), H == 0:
                  max e  s.t.  Rk-form  R(u,v,t) := (NU-2) s + s(u,u,1)+s(v,v,1)+s(t,t,1) + s(1,1,1)/(NU-1)
                  <= -e / C(NU,2) on Delta,  normalisation  sum_k tr F_k (+ sum_j a_j) = 1.
                  env DEL=D2 adds an explicit Delsarte term s += sum_{j<=D2} a_j (P_j(u)+P_j(v)+P_j(t))/3
                  (a_j >= 0).  Without DEL this is exactly the upstream kernel set (Legendre degree <= D/2 is
                  already contained in it, see test_addition).
  mu  D NU FRAC   as fixn, but e pinned to FRAC * e_max(D,NU) (read from results.jsonl) and maximise mu:
                  every PSD block is X + mu*I with X PSD (interior point for exact rounding); tr-normalised.
  test            unit tests: addition theorem, BV positivity and the dsum identity on random configs.
env: VERB=1, NOQ=1 (only linear + Gram multipliers, as upstream Case 1), THREADS (default 1).  Output: one json line per run appended to results.jsonl, solution npz in sol/.
"""
import os, sys, json, time, math
import numpy as np

if len(sys.argv) > 2:
    os.environ["POLYD"] = sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cvxpy as cp
from numpy.polynomial import legendre as Lg
import polyk
from polyk import (D, N3, LOWROWS, HIGHROWS, ONE, U, V, T, pmul, fidx, SYM_AVG, Yk_columns, LinPoly,
                   SOSProblem, subst_matrix, univ_embed, sos_columns, Qk, peval)

CUT = 0.5
THREADS = int(os.environ.get("THREADS", "1"))
DETG = ONE + 2 * pmul(pmul(U, V), T) - pmul(U, U) - pmul(V, V) - pmul(T, T)
SIZES = [D // 2 + 1 - k for k in range(D // 2 + 1)]
UROWS = np.array([fidx(j, 0, 0) for j in range(D + 1)])


def leg2mono(d2):
    M = np.zeros((D + 1, d2 + 1))
    for j in range(d2 + 1):
        e = np.zeros(j + 1); e[j] = 1
        c = Lg.leg2poly(e); M[:len(c), j] = c
    return M


class Prob(SOSProblem):
    def __init__(self, use_mu=False):
        super().__init__()
        self.use_mu = use_mu
        self.mu = cp.Variable(name="mu") if use_mu else None
        self.psdnames = []

    def psd(self, name, n):
        X = cp.Variable((n, n), PSD=True, name=name)
        self.vars[name] = X; self.psdnames.append(name)
        return X

    def blk(self, name):
        X = self.vars[name]
        return X + self.mu * np.eye(X.shape[0]) if self.use_mu else X

    def expr(self, lp, rows):
        e = lp.const[rows]
        for k, M in lp.terms.items():
            v = self.vars[k]
            vv = cp.vec(self.blk(k), order='C') if v.ndim == 2 else v
            e = e + np.asarray(M)[rows] @ vv
        return e

    def tri_nonneg(self, lp, tag):
        """lp >= 0 on Delta via Putinar SOS (blocks X (+mu I))."""
        for k, M in lp.terms.items():
            assert np.abs(np.asarray(M)[HIGHROWS]).max(initial=0) < 1e-12, (tag, k)
        d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
        blocks = [(ONE, d5)]
        for X in (U, V, T):
            blocks += [(ONE + X, d4), (CUT * ONE - X, d4)]
            if os.environ.get("NOQ") != "1":      # NOQ=1: drop the quadratic (1+x)(1/2-x) multipliers
                blocks.append((pmul(ONE + X, CUT * ONE - X), d4))
        if d3 >= 0:
            blocks.append((DETG, d3))
        rhs = 0
        for r, (g, d) in enumerate(blocks):
            Mg, n = sos_columns(g, d)
            nm = f"{tag}_B{r}"; self.psd(nm, n)
            rhs = rhs + Mg[LOWROWS] @ cp.vec(self.blk(nm), order='C')
        self.cons.append(self.expr(lp, LOWROWS) == rhs)

    def uni_nonneg(self, cexpr, tag, lo=-1.0, hi=CUT):
        """univariate polynomial with monomial coefficient expression cexpr (len D+1) >= 0 on [lo,hi]."""
        n0, n1 = D // 2 + 1, D // 2
        M0 = np.zeros((D + 1, n0 * n0)); M1 = np.zeros((D + 1, n1 * n1))
        g = [-lo * hi, lo + hi, -1.0]                      # (x-lo)(hi-x)
        for i in range(n0):
            for j in range(n0):
                M0[i + j, i * n0 + j] += 1
        for i in range(n1):
            for j in range(n1):
                for k, gk in enumerate(g):
                    M1[i + j + k, i * n1 + j] += gk
        self.psd(f"{tag}_U0", n0); self.psd(f"{tag}_U1", n1)
        self.cons.append(cexpr == M0 @ cp.vec(self.blk(f"{tag}_U0"), order='C')
                         + M1 @ cp.vec(self.blk(f"{tag}_U1"), order='C'))


def build_s(pr):
    s = LinPoly()
    for k, m in enumerate(SIZES):
        pr.psd(f"F{k}", m)
        s = s + LinPoly({f"F{k}": np.asarray(SYM_AVG @ Yk_columns(k, m))})
    return s


def sub(lp, spec):
    return lp.apply(subst_matrix(spec))


def solve(pr, obj, sense="max"):
    prob = cp.Problem(cp.Maximize(obj) if sense == "max" else cp.Minimize(obj), pr.cons)
    t0 = time.time()
    for tol in (1e-9, 1e-7):
        try:
            prob.solve(solver="CLARABEL", verbose=bool(int(os.environ.get("VERB", "0"))), tol_gap_abs=tol,
                       tol_gap_rel=tol, tol_feas=tol, max_iter=400, max_threads=THREADS)
            break
        except cp.error.SolverError as ex:
            print("solver failed at", tol, ex, flush=True)
    return prob, time.time() - t0


def record(res, xs=None):
    print(json.dumps(res), flush=True)
    with open(os.path.join(HERE, "results.jsonl"), "a") as fh:
        fh.write(json.dumps(res) + "\n")
    if xs is not None:
        os.makedirs(os.path.join(HERE, "sol"), exist_ok=True)
        np.savez(os.path.join(HERE, "sol", res["tag"] + ".npz"), meta=json.dumps(res),
                 **{k: np.asarray(v) for k, v in xs.items() if v is not None})


def run_bv(d2):
    use3 = os.environ.get("F3", "1") == "1"
    pr = Prob()
    s = build_s(pr) if use3 else LinPoly()
    a = cp.Variable(d2 + 1, nonneg=True, name="a"); pr.vars["a"] = a
    f = LinPoly({"a": univ_embed(0) @ leg2mono(d2)})
    if use3:
        pr.tri_nonneg(-1.0 * s, "T")
    pair = -1.0 * f - 3.0 * sub(s, (0, 0, 1.0)) if use3 else -1.0 * f
    pr.uni_nonneg(pr.expr(pair, UROWS) - np.eye(D + 1)[0], "P")
    s111 = pr.expr(sub(s, (1.0, 1.0, 1.0)), np.array([0]))[0] if use3 else 0
    obj = 1 + cp.sum(a) + s111
    prob, dt = solve(pr, obj, "min")
    tag = f"bv_D{D}_L{d2}" + ("" if use3 else "_lp")
    record(dict(tag=tag, mode="bv", D=D, D2=d2, three_point=use3, status=prob.status, bound=float(prob.value),
                time=round(dt, 1), sizes=SIZES if use3 else []), pr.xs())


def build_fixn(pr, nu, d2):
    s = build_s(pr)
    norm = sum(cp.trace(pr.blk(f"F{k}")) for k in range(len(SIZES)))
    if d2 is not None:
        a = cp.Variable(d2 + 1, nonneg=True, name="a"); pr.vars["a"] = a
        L2 = leg2mono(d2)
        delta = LinPoly({"a": (univ_embed(0) + univ_embed(1) + univ_embed(2)) @ L2 / 3.0})
        s = s + delta
        norm = norm + cp.sum(a)
    R = (nu - 2) * s + sub(s, (0, 0, 1.0)) + sub(s, (1, 1, 1.0)) + sub(s, (2, 2, 1.0)) \
        + sub(s, (1.0, 1.0, 1.0)) * (1.0 / (nu - 1))
    e = cp.Variable(1, name="e"); pr.vars["e"] = e
    C2 = nu * (nu - 1) / 2
    slack = -1.0 * R + LinPoly({"e": -polyk.pconst(1.0)[:, None] / C2})
    pr.tri_nonneg(slack, "T")
    pr.cons.append(norm == 1)
    return e[0]


def run_fixn(nu, d2):
    pr = Prob()
    e = build_fixn(pr, nu, d2)
    prob, dt = solve(pr, e, "max")
    tag = f"fixn_D{D}_n{nu:g}" + ("" if d2 is None else f"_del{d2}") + ("_noq" if os.environ.get("NOQ") == "1" else "")
    record(dict(tag=tag, mode="fixn", D=D, n=nu, delsarte=d2, status=prob.status, e=float(prob.value),
                e_over_C=float(prob.value) / (nu * (nu - 1) / 2), time=round(dt, 1), sizes=SIZES), pr.xs())


def run_mu(nu, frac, d2):
    tag0 = f"fixn_D{D}_n{nu:g}" + ("" if d2 is None else f"_del{d2}") + ("_noq" if os.environ.get("NOQ") == "1" else "")
    emax = None
    for line in open(os.path.join(HERE, "results.jsonl")):
        r = json.loads(line)
        if r["tag"] == tag0 and r["status"].startswith("optimal"):
            emax = r["e"]
    assert emax is not None and emax > 0, "run fixn first"
    pr = Prob(use_mu=True)
    e = build_fixn(pr, nu, d2)
    pr.cons += [e == frac * emax, pr.mu <= 1]
    prob, dt = solve(pr, pr.mu, "max")
    xs = pr.xs(); mu = float(pr.mu.value)
    mineig = min(float(np.linalg.eigvalsh(xs[k] + mu * np.eye(xs[k].shape[0]))[0]) for k in pr.psdnames)
    nblk = {k: xs[k].shape[0] for k in pr.psdnames}
    xs["mu"] = np.array(mu)
    record(dict(tag=tag0 + f"_mu{frac:g}", mode="mu", D=D, n=nu, delsarte=d2, frac=frac, e=frac * emax,
                status=prob.status, mu=mu, mineig=mineig, time=round(dt, 1), blocks=nblk), xs)


# ------------------------------------------------------------------------------------------- tests
def q_rec(k, u, v, t):
    q0, q1 = 1.0, t - u * v
    if k == 0:
        return q0
    for _ in range(k - 1):
        q0, q1 = q1, 2 * (t - u * v) * q1 - (1 - u * u) * (1 - v * v) * q0
    return q1


def test():
    rng = np.random.default_rng(1)
    # 1. addition theorem: P_k(t) = sum_m c_m P_k^{(m)}(u) P_k^{(m)}(v) Q_m(u,v,t), c_0=1, c_m = 2(k-m)!/(k+m)!
    worst = 0.0
    for k in range(0, 9):
        Pk = Lg.Legendre.basis(k)
        for _ in range(20):
            u, v, t = rng.uniform(-1, 1, 3)
            rhs = sum((1 if m == 0 else 2 * math.factorial(k - m) / math.factorial(k + m))
                      * Pk.deriv(m)(u) * Pk.deriv(m)(v) * q_rec(m, u, v, t) for m in range(k + 1))
            worst = max(worst, abs(rhs - Pk(t)))
    print("addition theorem max err", worst)
    # 2. random config of n unit vectors; random PSD F; BV positivity and dsum identity
    n = 13
    X = rng.normal(size=(n, 3)); X /= np.linalg.norm(X, axis=1)[:, None]
    G = X @ X.T; np.fill_diagonal(G, 1.0)
    s = np.zeros(N3)
    for k, m in enumerate(SIZES):
        A = rng.normal(size=(m, m)); F = A @ A.T / m
        s += np.asarray(SYM_AVG @ Yk_columns(k, m)) @ F.ravel()
    I, J, K = np.meshgrid(range(n), range(n), range(n), indexing='ij')
    I, J, K = I.ravel(), J.ravel(), K.ravel()
    sall = peval(s, G[I, J], G[I, K], G[J, K])
    Sall = sall.sum()
    # independent evaluation of sum over all triples of Y_k (unsymmetrised) via the recursion
    print("BV positivity: sum_all s =", Sall)
    R = (n - 2) * s + sub_np(s, (0, 0, 1.0)) + sub_np(s, (1, 1, 1.0)) + sub_np(s, (2, 2, 1.0)) \
        + sub_np(s, (1.0, 1.0, 1.0)) / (n - 1)
    dist = (I != J) & (I != K) & (J != K)
    lhs = peval(R, G[I, J], G[I, K], G[J, K])[dist].sum()
    Rw = (n - 1) * s + sub_np(s, (0, 0, 1.0)) + sub_np(s, (1, 1, 1.0)) + sub_np(s, (2, 2, 1.0)) \
        + sub_np(s, (1.0, 1.0, 1.0)) / (n - 1)
    print("  (control, wrong n-2 coefficient: dsum =", peval(Rw, G[I, J], G[I, K], G[J, K])[dist].sum(), ")")
    print("dsum identity: dsum R =", lhs, " (n-2) sum_all s =", (n - 2) * Sall, " rel err",
          abs(lhs - (n - 2) * Sall) / abs(Sall))
    # 3. polyk S3 vs direct recursion at a point
    k, m = 1, SIZES[1]
    cols = np.asarray(SYM_AVG @ Yk_columns(k, m)); u, v, t = 0.3, -0.2, 0.1
    direct = np.zeros((m, m))
    import itertools
    for (x, y, z) in itertools.permutations((u, v, t)):
        direct += np.outer(x ** np.arange(m), y ** np.arange(m)) * q_rec(k, x, y, z) / 6
    print("S3 vs recursion err", max(abs(peval(cols[:, i], u, v, t)[0] - direct.ravel()[i]) for i in range(m * m)))
    # 4. icosahedron
    ph = (1 + 5 ** 0.5) / 2
    P = []
    for a in (1, -1):
        for b in (ph, -ph):
            P += [(0, a, b), (a, b, 0), (b, 0, a)]
    P = np.array(P, float); P /= np.linalg.norm(P, axis=1)[:, None]
    Gi = P @ P.T; off = Gi[~np.eye(12, dtype=bool)]
    print("icosahedron: 12 points, max off-diag inner product", off.max(), " 1/sqrt5 =", 5 ** -0.5)


def sub_np(p, spec):
    return np.asarray(subst_matrix(spec) @ p)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "test":
        test()
    elif mode == "bv":
        run_bv(int(sys.argv[3]) if len(sys.argv) > 3 else D)
    elif mode == "fixn":
        dl = os.environ.get("DEL")
        run_fixn(float(sys.argv[3]), None if dl is None else int(dl))
    elif mode == "mu":
        dl = os.environ.get("DEL")
        run_mu(float(sys.argv[3]), float(sys.argv[4]), None if dl is None else int(dl))
