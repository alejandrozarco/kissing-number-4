"""Negative controls for check_cert_k4.py: tampered certificates must be rejected.
usage: python3 check_controls_k4.py cert_D14.json"""
import copy, json, os, subprocess, sys, tempfile
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
J0 = json.load(open(sys.argv[1]))


def bump(x):
    return str(Fr(x) + Fr(1, 2 ** 30))


cases = {
    "degree field -1 with a trivial false certificate": {"n": 25, "dim": 4, "D": -1, "cut": "1/2", "e": "1", "F": [[["1"]]], "SOS": []},
    "degree field 1 with a trivial false certificate": {"n": 25, "dim": 4, "D": 1, "cut": "1/2", "e": "1", "F": [[["1"]]], "SOS": []},
}
J = copy.deepcopy(J0); J["e"] = "1"; cases["margin e raised to 1"] = J
J = copy.deepcopy(J0); J["F"][0][0][0] = bump(J["F"][0][0][0]); cases["one kernel-block entry changed"] = J
J = copy.deepcopy(J0); B = J["SOS"][3]["B"]; B[1][2] = bump(B[1][2]); B[2][1] = B[1][2]; cases["one SOS entry changed (kept symmetric)"] = J
J = copy.deepcopy(J0); del J["SOS"][10]; cases["Gram-determinant block removed"] = J
J = copy.deepcopy(J0); J["SOS"][2]["g"] = "1+u"; cases["multiplier 1/2-u relabelled 1+u"] = J
J = copy.deepcopy(J0); J["n"] = 24; cases["n changed to 24"] = J
J = copy.deepcopy(J0); J["SOS"][1]["basis"][0] = [-1, 0, 0]; cases["negative exponent in a basis"] = J
bad = 0
for name, J in cases.items():
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        json.dump(J, fh)
    r = subprocess.run([sys.executable, os.path.join(HERE, "check_cert_k4.py"), fh.name], capture_output=True, text=True)
    os.unlink(fh.name)
    out = (r.stdout + r.stderr).strip().splitlines()
    ok = r.returncode != 0 and any("CERTIFICATE REJECTED" in l for l in out) and not any(l == "CERTIFICATE OK" for l in out)
    bad += not ok
    print(f"{'rejected' if ok else 'NOT REJECTED'}: {name}: {out[-1] if out else ''}")
print("ALL CONTROLS REJECTED" if bad == 0 else f"{bad} CONTROLS NOT REJECTED")
sys.exit(1 if bad else 0)
