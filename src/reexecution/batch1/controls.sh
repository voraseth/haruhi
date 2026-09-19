#!/bin/zsh
E=./mysweep
T=./mysweep_tr
L=./controls.log
echo "== B counterexample-multiset m2obj_620_23 census, mode1 ==" >> $L
$E 1 0 1 1 3 26 3 0 0 0 0 1 >> $L 2>&1
echo "== B same census, mode0 ==" >> $L
$E 1 0 1 1 3 26 3 0 0 0 0 0 >> $L 2>&1
echo "== C NEW 2-loop control: 3F5 + M2(2) + M2(3) + 25cyc, mode1 ==" >> $L
$E 3 0 0 0 0 25 2,3 0 0 0 0 1 >> $L 2>&1
echo "== C same, mode0 ==" >> $L
$E 3 0 0 0 0 25 2,3 0 0 0 0 0 >> $L 2>&1
echo "== C traced (tr engine) ==" >> $L
TRACE=1 $T 3 0 0 0 0 25 2,3 0 0 0 0 1 >> $L 2>&1
echo "== B traced ==" >> $L
TRACE=1 $T 1 0 1 1 3 26 3 0 0 0 0 1 >> $L 2>&1
echo "CONTROLS DONE" >> $L
