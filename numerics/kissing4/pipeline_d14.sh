#!/bin/bash
# After `./run.sh mu 14 25 0.5`: float check, exact rounding (2^-24, then finer if needed), independent exact check.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
while pgrep -f "k4.py mu 14 25" > /dev/null; do sleep 60; done
T=fixn_D14_n25_mu0.5
[ -f sol/$T.npz ] || { echo "PIPELINE: no interior solution"; exit 1; }
POLYD=14 nice -n 19 python3 k4.py check $T > logs/check_float_D14.log 2>&1; tail -1 logs/check_float_D14.log
for K in 24 28 32 40; do
  nice -n 19 python3 round_k4.py sol/$T.npz cert_D14.json $K > logs/round_cert_D14_K$K.log 2>&1
  if grep -q "^\[.*wrote cert_D14.json" logs/round_cert_D14_K$K.log; then echo "PIPELINE: rounded with KBITS=$K"; break; fi
  echo "PIPELINE: KBITS=$K failed: $(grep -E 'not positive|Error' logs/round_cert_D14_K$K.log | tail -1)"
done
[ -f cert_D14.json ] || { echo "PIPELINE: rounding failed"; exit 1; }
nice -n 19 python3 check_cert_k4.py cert_D14.json > logs/check_cert_D14.log 2>&1; tail -2 logs/check_cert_D14.log
echo PIPELINE DONE
