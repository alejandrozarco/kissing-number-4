#!/usr/bin/env python3
"""emit_k4.py -- 4D kissing certificate (numerics/kissing4/cert_D14.json) -> `Kissing4.CertK4` Lean data + chunked checks.

usage (always `nice -n 19`):
  python3 lean/gen/emit_k4.py numerics/kissing4/cert_D14.json [--outdir lean/Kissing4/Cert]

Same scheme as emit_k3.py (see there), with the S^3 kernel: the Lean kernel `Kissing4.Q4 k` is k! times the kernel
of the JSON, so the Lean kernel blocks are F~_k = F_k / k! (exact rationals) and ent_k / Λ = F_k / k!.
JSON semantics (numerics/kissing4, independently checked):
  -sum_k <F_k, Rk n k u v t> - e/C(n,2) = sum_r g_r(u,v,t) z_r^T B_r z_r   with g_r one of
  1, 1+x, 1/2-x, (1+x)(1/2-x) (x = u, v, t), detG.
Lean `CertK` (lean/Kissing/CertK.lean; 4D: lean/Kissing4/CertK.lean) with common denominator Λ: eps = Λ e, F_k = ent_k / Λ, and an SOS block with
multiplier codes `g` (codeK: 1+x -> 0..2, 1-2x -> 3..5, detG -> 6) contributes gKE(g) z^T ent z, which must equal
Λ g_r z^T B_r z.  Since 1-2x = 2 (1/2-x), ent_r = Λ B_r / c_r with c_r = 2 for the blocks containing 1/2-x, else 1.

Steps: integer data (Λ = Λ0 2^s, the first s for which every block packs into `Blk` = L D L^T + diagonally dominant
remainder, cert3_util.pack_psd); exact round trip back to the JSON rationals; simulation of every Lean Bool check
(Blk.ok, the piece statistics c1Stat with the Kronecker value, the composition kStat_idE, chk); emission.
"""
import argparse, hashlib, json, os, sys, time
from fractions import Fraction as Fr
from math import comb, lcm, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cert3_util as U

ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:6.1f}s]", *a, flush=True)


# ------------------------------------------------------------------ Python twins of lean/Kissing/CertK.lean
def codeK(code):
    if code in (0, 1, 2):
        return U.add(U.c(1), (U.U, U.V, U.T)[code])
    if code in (3, 4, 5):
        return U.sub(U.c(1), U.smul(2, (U.U, U.V, U.T)[code - 3]))
    if code == 6:
        return U.sub(U.add(U.c(1), U.smul(2, U.mul(U.U, U.mul(U.V, U.T)))),
                     U.add(U.sq(U.U), U.add(U.sq(U.V), U.sq(U.T))))
    return U.c(1)


def gKE(g):
    acc = U.c(1)
    for code in reversed(g):                       # List.foldr (fun code acc => mul (codeK code) acc) (c 1)
        acc = U.mul(codeK(code), acc)
    return acc


_q4 = {}


def q4E(k):
    """Kissing4.q4E, with exactly the Lean tree shape."""
    if k in _q4:
        return _q4[k]
    if k == 0:
        r = U.c(1)
    elif k == 1:
        r = U.sub(U.T, U.mul(U.U, U.V))
    else:
        j = k - 2
        r = U.sub(U.smul(2 * j + 3, U.mul(U.sub(U.T, U.mul(U.U, U.V)), q4E(j + 1))),
                  U.smul((j + 1) ** 2, U.mul(U.mul(U.sub(U.c(1), U.sq(U.U)), U.sub(U.c(1), U.sq(U.V))), q4E(j))))
    _q4[k] = r
    return r


def fk4E(r, b, k):
    return U.mul(U.fpE(r, b), q4E(k))


def kblkE(g, z, B):
    return U.mul(gKE(g), U.sqfE(B, z))


# multiplier name (JSON) -> (codeK list, c_r) with gKE(codes) = c_r * g_true
CODES = {"1": ([], 1), "detG": ([6], 1)}
for i, X in enumerate("uvt"):
    CODES[f"1+{X}"] = ([i], 1)
    CODES[f"1/2-{X}"] = ([3 + i], 2)
    CODES[f"(1+{X})(1/2-{X})"] = ([i, 3 + i], 2)


class Cert:
    def __init__(self, n, Lam, eps, F, S):
        self.n, self.Lam, self.eps, self.F, self.S = n, Lam, eps, F, S       # S: list of (g, z, Blk)

    def blk(self, k):
        return self.F[k] if k < len(self.F) else U.Blk([], [], [])

    def m(self, k):
        return len(self.blk(k).D)

    @property
    def K(self):
        return len(self.F)


def compose(cf, stF, stS):
    """kStat_idE."""
    n, C2 = cf.n, comb(cf.n, 2)
    return U.c1Sub(U.c1Sub(U.c1C(-(6 * (n - 1) * cf.eps)), U.c1Smul(C2, U.c1Sum(stF))),
                   U.c1Smul(6 * (n - 1) * C2, U.c1Sum(stS)))


def exact_int(q):
    assert q.denominator == 1, q
    return q.numerator


# ------------------------------------------------------------------ build
def build(J, s_step=4, s_max=200, theta=Fr(1, 2)):
    n, e = J["n"], Fr(J["e"])
    Fs = [[[Fr(x) / factorial(k) for x in row] for row in M] for k, M in enumerate(J["F"])]   # F~_k = F_k / k!
    blocks = []
    for b in J["SOS"]:
        codes, cr = CODES[b["g"]]
        blocks.append((b["g"], codes, cr, [tuple(z) for z in b["basis"]], [[Fr(x) / cr for x in row] for row in b["B"]]))
    L0 = e.denominator
    for x in [x for M in Fs for row in M for x in row] + [x for blk in blocks for row in blk[4] for x in row]:
        L0 = lcm(L0, x.denominator)
    s = 0
    while True:
        Lam = L0 << s
        good, Fb, Sb, infos = True, [], [], {}
        for k, M in enumerate(Fs):
            b, info = U.pack_psd([[exact_int(x * Lam) for x in row] for row in M], theta)
            infos[f"F{k}"] = info
            if b is None or not info["ok"]:
                good = False; break
            Fb.append(b)
        if good:
            for i, (nm, codes, cr, z, B) in enumerate(blocks):
                b, info = U.pack_psd([[exact_int(x * Lam) for x in row] for row in B], theta)
                infos[f"S{i}"] = info
                if b is None or not info["ok"]:
                    good = False; break
                Sb.append((codes, z, b))
        if good:
            break
        bad = list(infos)[-1]
        log(f"  Λ = Λ0·2^{s}: packing failed at {bad}: {infos[bad].get('why', 'Δ not diagonally dominant')}")
        s += s_step
        if s > s_max:
            raise SystemExit("no Λ found")
    cf = Cert(n, Lam, exact_int(e * Lam), Fb, Sb)
    log(f"Λ = Λ0·2^{s}, Λ0 = {L0} ({L0.bit_length()} bits), Λ: {Lam.bit_length()} bits; eps = {cf.eps}")
    # exact round trip to the JSON rationals
    assert Fr(cf.eps, Lam) == e
    for k, M in enumerate(Fs):
        r = cf.m(k)
        assert [[Fr(cf.blk(k).ent(r, a, b), Lam) for b in range(r)] for a in range(r)] == M, f"F{k} round trip"
        assert [[Fr(cf.blk(k).ent(r, a, b), Lam) * factorial(k) for b in range(r)] for a in range(r)] == \
            [[Fr(x) for x in row] for row in J["F"][k]], f"F{k} round trip (JSON)"
    for i, ((codes, z, b), blk) in enumerate(zip(cf.S, J["SOS"])):
        r = len(z)
        cr = CODES[blk["g"]][1]
        assert [[Fr(b.ent(r, a, c), Lam) * cr for c in range(r)] for a in range(r)] == \
            [[Fr(x) for x in row] for row in blk["B"]], f"S{i} round trip"
        assert [list(t) for t in z] == blk["basis"]
    log("exact round trip: the integer data encode exactly the JSON rationals")
    return cf, dict(L0=L0, s=s, pack={k: {"eps_shift": str(v["eps"]), "dd_slack": str(v["dd_slack"])}
                                      for k, v in infos.items()})


def simulate(cf):
    rep = {"n_ge_3": cf.n >= 3, "Lam_pos": cf.Lam > 0, "K_le_8": cf.K <= 8,
           "F_ok": [cf.blk(k).ok(cf.m(k)) for k in range(cf.K)],
           "S_ok": [b.ok(len(z)) for (_, z, b) in cf.S]}
    pF = [U.c1FtotK(cf.n, fk4E(cf.m(k), cf.blk(k), k)) for k in range(cf.K)]
    pS = [kblkE(g, z, b) for (g, z, b) in cf.S]
    lF = [U.stat_l(e) for e in pF]
    lS = [U.stat_l(e) for e in pS]
    tot0 = compose(cf, [x + (0,) for x in lF], [x + (0,) for x in lS])
    w, D = U.chk_params(*tot0[:4])
    log(f"Kronecker parameters w = {w}, D = {D}; computing the Kronecker values of {len(pF) + len(pS)} pieces ...")
    stF = [l + (U.kev(e, w, D),) for l, e in zip(lF, pF)]
    stS = [l + (U.kev(e, w, D),) for l, e in zip(lS, pS)]
    tot = compose(cf, stF, stS)
    rep.update(w=w, D=D, stF=stF, stS=stS, total=tot, chk=(tot[4] == 0 and U.chk_params(*tot[:4]) == (w, D)))
    rep["check"] = rep["n_ge_3"] and rep["Lam_pos"] and rep["K_le_8"] and all(rep["F_ok"]) and all(rep["S_ok"]) and rep["chk"]
    return rep


# ------------------------------------------------------------------ chunked SOS-block checks
CH = 10                                            # rows per chunk


def chunks(r):
    """[(start, length)] of the row chunks of a block of size r."""
    return [(s0, min(CH, r - s0)) for s0 in range(0, r, CH)]


def sqT(b, z, q):
    """Kissing4.sqT."""
    r = len(z)
    return U.smulNZ(b.dq(q), U.sq(U.sumRange(r, lambda a: U.smulNZ(b.lq(q, a), U.zmon(z, a)))))


def delR(b, z, a):
    """Kissing4.delR."""
    r = len(z)
    return U.sumRange(r, lambda c: U.smulNZ(b.dl(a, c), U.zzmon(z, a, c)))


def okRow(b, r, i):
    """Kissing4.okRow: the row-i part of Blk.ok."""
    return (0 <= b.dq(i)) and all(b.dl(i, j) == b.dl(j, i) for j in range(r)) and \
        sum((0 if i == j else abs(b.dl(i, j))) for j in range(r)) <= b.dl(i, i)


def chunk_data(cf, rep):
    """Per SOS block: the chunk statistics (as emitted); asserts that composing them reproduces the statistic of the
    whole block (rep["stS"]) and that the rowwise okRow agrees with Blk.ok."""
    w, D = rep["w"], rep["D"]
    out = []
    for i, (g, z, b) in enumerate(cf.S):
        r = len(z)
        ch = chunks(r)
        sq_rows, del_rows, res = [], [], []
        for j, (s0, ln) in enumerate(ch):
            sqs = [U.c1Stat(sqT(b, z, q), w, D) for q in range(s0, s0 + ln)]
            dls = [U.c1Stat(delR(b, z, a), w, D) for a in range(s0, s0 + ln)]
            assert all(okRow(b, r, q) for q in range(s0, s0 + ln)), f"S{i} chunk {j}: okRow"
            res.append(dict(s=s0, len=ln, sq=U.c1Sum(sqs), dl=U.c1Sum(dls)))
            sq_rows += sqs
            del_rows += dls
        assert b.ok(r) is True
        gst = U.c1Stat(gKE(g), w, D)
        whole = tuple(rep["stS"][i])
        assert U.c1Mul(gst, U.c1Add(U.c1Sum(sq_rows), U.c1Sum(del_rows))) == whole, f"S{i}: rows"
        acc_sq, acc_dl = res[0]["sq"], res[0]["dl"]
        for c in res[1:]:
            acc_sq, acc_dl = U.c1Add(acc_sq, c["sq"]), U.c1Add(acc_dl, c["dl"])
        assert U.c1Mul(gst, U.c1Add(acc_sq, acc_dl)) == whole, f"S{i}: chunk sums"
        log(f"  S{i}: r = {r}, chunks {[(c['s'], c['len']) for c in res]}: composition reproduces the whole-block statistic")
        out.append(res)
    return out


# ------------------------------------------------------------------ emission
HDR = ("/-! {what}\n\nGenerated by `lean/gen/emit_k4.py` from `numerics/kissing4/{src}` (sha256 {sha}).\n"
       "Do not edit; regenerate. -/\n")
NS = "Kissing4.Cert"


def blk_lean(name, b, r):
    Bd = U.field_width(b.d)
    Bl = U.field_width([v for col in b.l for v in col])
    BD = U.field_width([v for row in b.D for v in row])
    xd, xl, xD = U.packI(Bd, b.d), U.packM(Bl, b.l), U.packM(BD, b.D)
    back = U.mkBlk(r, Bd, Bl, BD, xd, xl, xD)
    assert back.d == b.d and back.l == b.l and back.D == b.D, "mkBlk round trip"
    return f"def {name} : Blk := mkBlk {r} {Bd} {Bl} {BD}\n  {hex(xd)}\n  {hex(xl)}\n  {hex(xD)}"


def blk_rows_lean(name, b, r):
    """One definition per row (pivots, columns of L, rows of Δ) instead of one packed number, so that a kernel check of
    row s does not have to decode the rows before it."""
    Bd = U.field_width(b.d)
    Bl = U.field_width([v for col in b.l for v in col])
    BD = U.field_width([v for row in b.D for v in row])
    assert len(b.d) == r and len(b.l) == r and len(b.D) == r and all(len(x) == r for x in b.l + b.D)
    xd = U.packI(Bd, b.d)
    xl = [U.packI(Bl, col) for col in b.l]
    xD = [U.packI(BD, row) for row in b.D]
    assert U.unpackI(Bd, r, xd) == b.d and [U.unpackI(Bl, r, x) for x in xl] == b.l and \
        [U.unpackI(BD, r, x) for x in xD] == b.D, "per-row round trip"
    out = [f"def {name}_d : List Int := unpackI {Bd} {r} {hex(xd)}"]
    out += [f"def {name}_l_{q} : List Int := unpackI {Bl} {r} {hex(x)}" for q, x in enumerate(xl)]
    out += [f"def {name}_D_{a} : List Int := unpackI {BD} {r} {hex(x)}" for a, x in enumerate(xD)]
    out.append(f"def {name} : Blk := ⟨{name}_d, [{', '.join(f'{name}_l_{q}' for q in range(r))}], "
               f"[{', '.join(f'{name}_D_{a}' for a in range(r))}]⟩")
    return "\n".join(out)


def emit(cf, rep, src, sha, outdir, cd):
    os.makedirs(outdir, exist_ok=True)
    w, D = rep["w"], rep["D"]
    files = {}
    L = ["import Kissing4.CertK", "import Kissing4.Chunk",
         HDR.format(what="The exact kissing certificate for `n = 25` in the `Kissing4.CertK4` format (common denominator "
                         "`Λ = lam_`).\n\n* margin `eps_ / lam_ = e > 0`;\n"
                         "* `F0..F7`: kernel blocks, `F_k = ent_k / lam_` (for the `S³` kernel `Q4 k`, i.e. the JSON block divided by `k!`), `ent = ∑_q d_q l_q l_qᵀ + Δ` "
                         "(`Δ` diagonally dominant);\n"
                         "* `S0..`: SOS blocks (multiplier codes of `Kissing.codeK`, monomial basis `z`).\n"
                         "The `F` blocks are packed by `ThomsonN7.Cert.mkBlk`, the SOS blocks row by row by `ThomsonN7.Cert.unpackI` (offset-binary fields, least significant first).",
                    src=src, sha=sha),
         "namespace Kissing4", "namespace Cert", "open ThomsonN7.Cert Kissing\n",
         f"def lam_ : Nat := {cf.Lam}", f"def eps_ : Int := {U.lint(cf.eps)}"]
    for k, b in enumerate(cf.F):
        L.append(blk_lean(f"F{k}", b, cf.m(k)))
    for i, (g, z, b) in enumerate(cf.S):
        L.append(f"def S{i}_z : List (Nat × Nat × Nat) := {U.lz_list(z)}")
        L.append(blk_rows_lean(f"S{i}_B", b, len(z)))
        L.append(f"def S{i} : KBlk := ⟨[{', '.join(U.lnat(x) for x in g)}], S{i}_z, S{i}_B⟩")
    L.append("def cf : CertK4 :=")
    L.append(f"  {{ n := {U.lnat(cf.n)}, Lam := lam_, eps := eps_,")
    L.append("    F := [" + ", ".join(f"F{k}" for k in range(cf.K)) + "],")
    L.append("    S := [" + ", ".join(f"S{i}" for i in range(len(cf.S))) + "] }")
    L += ["\nend Cert", "end Kissing4\n"]
    files["Data.lean"] = "\n".join(L)
    # ---------------- one module per piece group
    stmt, lit = {}, {}
    for k in range(cf.K):
        stmt[f"F{k}"] = (f"ThomsonN7.Case1.c1Stat {w} {D} (ThomsonN7.Case1.c1FtotK cf.n (fk4E (cf.m {k}) (cf.blk {k}) {k}))")
        lit[f"F{k}"] = rep["stF"][k]
    thm = {nm: f"theorem stat_{nm} :\n    {stmt[nm]} = {U.stat_lit(lit[nm])} := by\n  decide +kernel\n" for nm in stmt}
    # (module, header text, body) in chain order
    mods = [(f"ChkF{k}", f"Kronecker statistics of the piece F{k} of the 4D kissing certificate (`w = {w}`, `D = {D}`), "
                         f"one `decide +kernel` per declaration.", thm[f"F{k}"]) for k in range(cf.K)]
    C1 = "ThomsonN7.Case1"
    for i, (g, z, b) in enumerate(cf.S):
        r = len(z)
        res, ch = cd[i], chunks(r)
        for j, c in enumerate(res):
            s0, ln = c["s"], c["len"]
            body = "\n".join([
                f"theorem stS{i}_sq_{j} : {C1}.c1Sum ((List.range' {s0} {ln}).map fun q => {C1}.c1Stat {w} {D} "
                f"(sqT S{i}_B S{i}_z q)) = {U.stat_lit(c['sq'])} := by",
                "  decide +kernel\n",
                f"theorem stS{i}_del_{j} : {C1}.c1Sum ((List.range' {s0} {ln}).map fun a => {C1}.c1Stat {w} {D} "
                f"(delR S{i}_B S{i}_z a)) = {U.stat_lit(c['dl'])} := by",
                "  decide +kernel\n",
                f"theorem okS{i}_{j} : (List.range' {s0} {ln}).all (okRow {r} S{i}_B) = true := by",
                "  decide +kernel\n"])
            mods.append((f"ChkS{i}_{j}", f"Row chunk {j} (rows {s0} to {s0 + ln - 1}) of the checks of the SOS block `S{i}` of the 4D kissing "
                                          f"certificate (`w = {w}`, `D = {D}`): statistics of the `L D Lᵀ` rows and of the remainder rows, "
                                          f"and `Blk.ok` of these rows; one `decide +kernel` per declaration.", body))
        rng = " ++ ".join(f"List.range' {c['s']} {c['len']}" for c in res)
        nsq = ", ".join(f"stS{i}_sq_{j}" for j in range(len(res)))
        ndl = ", ".join(f"stS{i}_del_{j}" for j in range(len(res)))
        nok = ", ".join(f"okS{i}_{j}" for j in range(len(res)))
        stat_lines = [f"theorem stat_S{i} : {C1}.c1Stat {w} {D} (kblkE S{i}) = {U.stat_lit(rep['stS'][i])} := by",
                      "  rw [c1Stat_kblkE]",
                      f"  show {C1}.c1Mul ({C1}.c1Stat {w} {D} (Kissing.gKE S{i}.g)) ({C1}.c1Add "
                      f"({C1}.c1Sum ((List.range S{i}_z.length).map fun q => {C1}.c1Stat {w} {D} (sqT S{i}_B S{i}_z q))) "
                      f"({C1}.c1Sum ((List.range S{i}_z.length).map fun a => {C1}.c1Stat {w} {D} (delR S{i}_B S{i}_z a)))) = _",
                      f"  rw [show S{i}_z.length = {r} from rfl, show List.range {r} = {rng} from rfl]"]
        if len(res) > 1:
            stat_lines.append("  simp only [List.map_append, c1Sum_append]")
        stat_lines += [f"  rw [{nsq}, {ndl}]", "  decide +kernel\n"]
        ok_lines = [f"theorem ok_S{i} : S{i}.B.ok S{i}.z.length = true := by",
                    f"  show S{i}_B.ok S{i}_z.length = true",
                    f"  rw [show S{i}_z.length = {r} from rfl, ok_eq_all_okRow, show List.range {r} = {rng} from rfl]",
                    f"  simp only [List.all_append, {nok}, Bool.and_self]\n" if len(res) > 1 else
                    f"  simp only [{nok}]\n"]
        mods.append((f"ChkS{i}", f"Composition of the row chunks of the SOS block `S{i}` of the 4D kissing certificate: the "
                                  f"Kronecker statistics `stat_S{i}` (`w = {w}`, `D = {D}`) and `ok_S{i}`.",
                     "\n".join(stat_lines + ok_lines)))
    groups = [(g, []) for g, _, _ in mods]
    # The modules form one linear import chain (Data, ChkF0..ChkF7, ChkS0_0, ..., ChkS0, ChkS1_0, ..., ChkS10, ChkId, OkF,
    # Check), so that a `lake build` (which cannot limit its parallelism) compiles them one at a time on a shared machine.
    prev = "Data"
    for g, what, body in mods:
        files[f"{g}.lean"] = "\n".join([
            f"import Kissing4.Cert.{prev}",
            HDR.format(what=what, src=src, sha=sha),
            "namespace Kissing4", "namespace Cert", "open ThomsonN7.Cert Kissing\n"]) + body + \
            "\nend Cert\nend Kissing4\n"
        prev = g
    tot = rep["total"]
    pieces_rw = ", ".join([f"stat_F{k}" for k in range(cf.K)] + [f"stat_S{i}" for i in range(len(cf.S))])
    Slist = ", ".join(f"S{i}" for i in range(len(cf.S)))
    rng = ", ".join(str(k) for k in range(cf.K))
    head2 = lambda imports, what, attr="": "\n".join(["\n".join(f"import Kissing4.Cert.{g}" for g in imports)
                                              + ("\n\n" + attr if attr else ""),
                                              HDR.format(what=what, src=src, sha=sha),
                                              "namespace Kissing4", "namespace Cert", "open ThomsonN7.Cert Kissing\n"])
    tail2 = "end Cert\nend Kissing4\n"
    # the identity: composition of the piece statistics and the Kronecker check
    files["ChkId.lean"] = head2([groups[-1][0]],
        "The Kronecker check of the identity of the kissing certificate: composition of the piece statistics\n"
        f"(ℓ¹ < 2^{w}, degrees < {D}, Kronecker value 0; soundness: `Kron.Ex.ev_eq_zero_of_kev`).",
        "-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):\n"
        "-- `cf_idE_stat` from `Case1.c1_idE_stat`, `cf_chk` from `Case1.cf_chk`, `cf_K`, `cf_S`, `cf_range` from\n"
        "-- `Case1.c1_K`, `Case1.c1_S`, `Case1.c1_range4`.") + "\n".join([
        f"theorem cf_K : cf.K = {cf.K} := rfl\n",
        f"theorem cf_S : cf.S = [{Slist}] := rfl\n",
        f"theorem cf_range : List.range {cf.K} = [{rng}] := rfl\n",
        f"/-- The statistics of the whole identity expression: `ℓ¹`-norm below `2 ^ {w}`, degrees "
        f"`{tot[1]}, {tot[2]}, {tot[3]}`, Kronecker value `0`. -/",
        f"theorem cf_idE_stat : ThomsonN7.Case1.c1Stat {w} {D} cf.idE = "
        f"({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int)) := by",
        "  rw [kStat_idE4, cf_K, cf_S, cf_range]",
        "  simp only [List.map_cons, List.map_nil]",
        f"  rw [{pieces_rw}]",
        "  decide +kernel\n",
        "/-- The Kronecker check of the identity expression. -/",
        "theorem cf_chk : chk cf.idE = true := by",
        f"  have h := ThomsonN7.Case1.c1Stat_eq {w} {D} cf.idE",
        "  rw [cf_idE_stat] at h",
        "  simp only [Prod.mk.injEq] at h",
        "  obtain ⟨hl, hx, hy, hz, hk⟩ := h",
        "  unfold chk",
        "  rw [← hl, ← hx, ← hy, ← hz]",
        f"  have hW : Nat.log2 {tot[0]} + 1 = {w} := by decide +kernel",
        f"  have hD : max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {D} := by decide +kernel",
        "  rw [hW, hD]",
        "  exact decide_eq_true hk.symm\n"]) + "\n" + tail2
    # positive semidefiniteness data, one module for the F-blocks and one per SOS block
    files["OkF.lean"] = head2(["ChkId"], "`Blk.ok` of the kernel blocks of the kissing certificate.",
        "-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):\n"
        "-- `cf_blocks` from `Case1.cf_blocks`.") + "\n".join([
        "/-- The positive-semidefiniteness certificates of the `F`-blocks. -/",
        "theorem cf_blocks : (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) = true := by",
        "  decide +kernel\n"]) + "\n" + tail2
    oks = ", ".join(f"ok_S{i}" for i in range(len(cf.S)))
    files["Check.lean"] = head2(["OkF"],
        "Assembly of the chunked check: `Kissing4.Cert.cf.check = true`.",
        "-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):\n"
        "-- `cf_sos` from `Case1.cf_sos`, `cf_ok` from `Case1.cf_ok`.") + "\n".join([
        "/-- The positive-semidefiniteness certificates of the SOS blocks. -/",
        "theorem cf_sos : cf.S.all (fun s => s.B.ok s.z.length) = true := by",
        "  rw [cf_S]",
        f"  simp only [List.all_cons, List.all_nil, {oks}, Bool.and_true]\n",
        "/-- The kissing certificate passes the exact check. -/",
        "theorem cf_ok : cf.check = true := by",
        "  unfold CertK4.check",
        "  rw [cf_chk, cf_blocks, cf_sos]",
        "  decide +kernel\n",
        "/-- The margin is positive. -/",
        "theorem cf_eps_pos : 0 < cf.eps := by decide +kernel\n",
        "/-- The certificate is for `25` points. -/",
        "theorem cf_n : cf.n = 25 := rfl\n"]) + "\n" + tail2
    for nm, txt in files.items():
        with open(os.path.join(outdir, nm), "w") as fh:
            fh.write(txt)
    return files, groups


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--outdir", default=os.path.join(ROOT, "lean", "Kissing4", "Cert"))
    a = ap.parse_args()
    raw = open(a.cert, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    J = json.loads(raw)
    cf, meta = build(J)
    rep = simulate(cf)
    log(f"Blk.ok: F {rep['F_ok']}, S {rep['S_ok']}; chk {rep['chk']}; total stat {rep['total'][:4]} kev {rep['total'][4]}")
    assert rep["check"], "the Lean check would fail"
    files, groups = emit(cf, rep, os.path.basename(a.cert), sha, a.outdir, chunk_data(cf, rep))
    for nm, txt in files.items():
        log(f"  wrote {nm}: {len(txt) // 1024} KiB")
    with open(os.path.join(a.outdir, "emit_report.json"), "w") as fh:
        json.dump({"cert": os.path.basename(a.cert), "sha256": sha, "Lam_bits": cf.Lam.bit_length(), **meta,
                   "w": rep["w"], "D": rep["D"], "total": [str(x) for x in rep["total"]],
                   "groups": [g for g, _ in groups] + ["ChkId", "OkF", "Check"],
                   "chunk_rows": CH}, fh, indent=1)


if __name__ == "__main__":
    main()
