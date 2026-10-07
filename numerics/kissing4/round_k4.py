"""Exact rounding of the 4D fixed-n = 25 interior solution (k4.py mode mu): ../kissing3/round_k3.py with the kernels
of S^3, Q_{k+1} = ((2k+1) w Q_k - k g Q_{k-1}) / (k+1) (Legendre), in exact rational arithmetic.
usage: python3 round_k4.py sol/fixn_D14_n25_mu0.5.npz cert_D14.json [KBITS] [E]"""
import json, os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "kissing3"))
import round_k3 as R


def Qs4(kmax):
    w = R.padd(R.T, R.pmul(R.U, R.V), -1)
    g = R.pmul(R.padd(R.ONE, R.pmul(R.U, R.U), -1), R.padd(R.ONE, R.pmul(R.V, R.V), -1))
    Q = [R.ONE, w]
    k = 1
    while len(Q) <= kmax:
        Q.append(R.pscale(R.padd(R.pscale(R.pmul(w, Q[-1]), Fr(2 * k + 1)), R.pmul(g, Q[-2]), -k), Fr(1, k + 1)))
        k += 1
    return Q


R.Qs = Qs4
if __name__ == "__main__":
    a = sys.argv
    out = a[2]
    R.main(a[1], out, int(a[3]) if len(a) > 3 else 24, Fr(a[4]) if len(a) > 4 else Fr(1, 32))
    J = json.load(open(out))
    J["dim"] = 4
    J["claim"] = ("dimension 4 (kernels of S^3): for all (u,v,t) with GramOK and u,v,t <= 1/2:  "
                  "sum_k <F_k, Rk n k u v t> <= -e / C(n,2)")
    json.dump(J, open(out, "w"))
