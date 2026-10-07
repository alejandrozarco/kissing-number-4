"""Kissing number in dimension 4: three-point SDP feasibility probe (floating point), reusing ../kissing3/k3.py.

Changes from dimension 3 (Bachoc-Vallentin, kernels for S^3):
  * Q_k(u,v,t) = ((1-u^2)(1-v^2))^{k/2} P_k((t-uv)/sqrt((1-u^2)(1-v^2))) with P_k the Legendre polynomials
    (Gegenbauer for S^2) instead of Chebyshev:  Q_{k+1} = ((2k+1) w Q_k - k g Q_{k-1}) / (k+1),
    w = t - uv, g = (1-u^2)(1-v^2);
  * the two-point (Delsarte) part uses the Gegenbauer polynomials of S^3, U_j(x)/(j+1) (normalised to 1 at x = 1);
  * the region is unchanged: Gram triples of three unit vectors (any dimension >= 3) with u, v, t <= 1/2.
usage: python3 k4.py test | bv D [D2] | fixn D N | mu D N FRAC | check TAG      (outputs in this directory)
"""
import os, sys, math, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
K3 = os.path.join(os.path.dirname(HERE), "kissing3")
if len(sys.argv) > 2 and sys.argv[1] != "check":
    os.environ["POLYD"] = sys.argv[2]
sys.path.insert(0, K3)
import numpy as np
import polyk
from polyk import ONE, U, V, T, pmul, peval, SYM_AVG


def Qk4(kmax):
    w = T - pmul(U, V)
    g = pmul(ONE - pmul(U, U), ONE - pmul(V, V))
    Q = [ONE.copy(), w.copy()]
    k = 1
    while len(Q) <= kmax:
        Q.append(((2 * k + 1) * pmul(w, Q[-1]) - k * pmul(g, Q[-2])) / (k + 1))
        k += 1
    return Q


polyk.Qk = Qk4
import k3                                  # noqa: E402  (uses polyk.Yk_columns -> polyk.Qk, now patched)
k3.HERE = HERE


def geg2mono(d2):
    """columns: monomial coefficients (length D+1) of U_j(x)/(j+1), j = 0..d2."""
    D = polyk.D
    M = np.zeros((D + 1, d2 + 1))
    Up = [np.array([1.0]), np.array([0.0, 2.0])]
    while len(Up) <= d2:
        a = np.concatenate([[0.0], 2 * Up[-1]]); b = np.concatenate([Up[-2], [0.0, 0.0]])
        Up.append(a - b)
    for j in range(d2 + 1):
        M[:len(Up[j]), j] = Up[j] / (j + 1)
    return M


k3.leg2mono = geg2mono


def q_rec4(k, u, v, t):
    w, g = t - u * v, (1 - u * u) * (1 - v * v)
    q0, q1 = 1.0, w
    if k == 0:
        return q0
    for j in range(1, k):
        q0, q1 = q1, ((2 * j + 1) * w * q1 - j * g * q0) / (j + 1)
    return q1


def test():
    rng = np.random.default_rng(1)
    D = polyk.D
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    # 1. Q_k from polyk equals the closed form with Legendre P_k
    from numpy.polynomial import legendre as Lg
    worst = 0.0
    Q = Qk4(D // 2)
    for _ in range(50):
        u, v, t = rng.uniform(-0.95, 0.95, 3)
        g = (1 - u * u) * (1 - v * v)
        for k in range(D // 2 + 1):
            ref = g ** (k / 2) * Lg.Legendre.basis(k)((t - u * v) / math.sqrt(g))
            worst = max(worst, abs(peval(Q[k], u, v, t)[0] - ref), abs(q_rec4(k, u, v, t) - ref))
    print("Q_k vs Legendre closed form: max err", worst)
    # 2. BV positivity on S^3 and the dsum identity, random configurations of 25 points in R^4
    for trial in range(3):
        n = 25
        X = rng.normal(size=(n, 4)); X /= np.linalg.norm(X, axis=1)[:, None]
        G = X @ X.T; np.fill_diagonal(G, 1.0)
        I, J, K = (a.ravel() for a in np.meshgrid(range(n), range(n), range(n), indexing="ij"))
        mins = []
        for k, m in enumerate(sizes):
            cols = np.asarray(SYM_AVG @ polyk.Yk_columns(k, m))
            M = np.zeros((m, m))
            for c in range(m * m):
                M.flat[c] = peval(cols[:, c], G[I, J], G[I, K], G[J, K]).sum()
            mins.append(np.linalg.eigvalsh((M + M.T) / 2)[0] / max(1.0, abs(M).max()))
        print(f"BV positivity, trial {trial}: min relative eigenvalue of sum_ijl S_k over k:", min(mins))
    s = np.zeros(polyk.N3)
    for k, m in enumerate(sizes):
        A = rng.normal(size=(m, m)); F = A @ A.T / m
        s += np.asarray(SYM_AVG @ polyk.Yk_columns(k, m)) @ F.ravel()
    sub = k3.sub_np
    R = (n - 2) * s + sub(s, (0, 0, 1.0)) + sub(s, (1, 1, 1.0)) + sub(s, (2, 2, 1.0)) + sub(s, (1.0, 1.0, 1.0)) / (n - 1)
    dist = (I != J) & (I != K) & (J != K)
    lhs = peval(R, G[I, J], G[I, K], G[J, K])[dist].sum()
    Sall = peval(s, G[I, J], G[I, K], G[J, K]).sum()
    print("dsum identity rel err", abs(lhs - (n - 2) * Sall) / abs(Sall))
    # 3. the 24-cell: 24 points, max off-diagonal inner product 1/2
    P = [v for v in itertools.product((-1, 0, 1), repeat=4) if sum(abs(x) for x in v) == 2]
    P = np.array(P, float) / math.sqrt(2)
    Gc = P @ P.T
    print("24-cell (D4 roots): points", len(P), " max off-diagonal inner product", Gc[~np.eye(len(P), dtype=bool)].max())


def check(tag):
    """float check of a fixn/mu solution: max of R over the region by dense sampling; eigenvalues."""
    Z = np.load(os.path.join(HERE, "sol", tag + ".npz"), allow_pickle=True)
    meta = json.loads(str(Z["meta"]))
    D, n = meta["D"], meta["n"]
    os.environ["POLYD"] = str(D)
    assert polyk.D == D, "run check with the same POLYD: python3 k4.py check TAG (sets it from the tag)"
    mu = float(meta.get("mu", 0.0))
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    s = np.zeros(polyk.N3)
    mine = []
    for k, m in enumerate(sizes):
        F = Z[f"F{k}"] + mu * np.eye(m)
        mine.append(np.linalg.eigvalsh(F)[0])
        s += np.asarray(SYM_AVG @ polyk.Yk_columns(k, m)) @ F.ravel()
    sub = k3.sub_np
    R = (n - 2) * s + sub(s, (0, 0, 1.0)) + sub(s, (1, 1, 1.0)) + sub(s, (2, 2, 1.0)) + sub(s, (1.0, 1.0, 1.0)) / (n - 1)
    rng = np.random.default_rng(0)
    pts = rng.uniform(-1, 0.5, size=(3_000_000, 3))
    g = pts[:, 0] ** 2 + pts[:, 1] ** 2 + pts[:, 2] ** 2
    ok = 1 + 2 * pts[:, 0] * pts[:, 1] * pts[:, 2] - g >= 0
    pts = pts[ok]
    grid = np.linspace(-1, 0.5, 61)
    gp = np.array([(a, b, c) for a in grid for b in grid for c in grid])
    gp = gp[1 + 2 * gp[:, 0] * gp[:, 1] * gp[:, 2] - (gp ** 2).sum(1) >= -1e-12]
    allp = np.vstack([pts, gp])
    vals = peval(R, allp[:, 0], allp[:, 1], allp[:, 2])
    i = int(np.argmax(vals))
    C = n * (n - 1) / 2
    out = dict(tag=tag, n=n, D=D, e=meta["e"], claimed_maxR=-meta["e"] / C, sampled_maxR=float(vals[i]),
               argmax=[round(float(x), 6) for x in allp[i]], n_samples=int(len(allp)), F_mineig=float(min(mine)),
               OK=bool(vals[i] < 0 and min(mine) > 0))
    print(json.dumps(out))
    with open(os.path.join(HERE, "checks.jsonl"), "a") as fh:
        fh.write(json.dumps(out) + "\n")


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "test":
        test()
    elif mode == "bv":
        k3.run_bv(int(sys.argv[3]) if len(sys.argv) > 3 else polyk.D)
    elif mode == "fixn":
        dl = os.environ.get("DEL")
        k3.run_fixn(float(sys.argv[3]), None if dl is None else int(dl))
    elif mode == "mu":
        dl = os.environ.get("DEL")
        k3.run_mu(float(sys.argv[3]), float(sys.argv[4]), None if dl is None else int(dl))
    elif mode == "check":
        check(sys.argv[2])
