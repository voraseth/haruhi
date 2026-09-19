#!/bin/zsh
E=./mysweep
T=./mysweep_tr
L=./controls2.log
echo "== D d4-closure control: 3F5+S3+M2(2)+25cyc nd4=1 mode1 ==" >> $L
$E 3 0 1 0 0 25 2 0 1 0 0 1 >> $L 2>&1
echo "== D traced ==" >> $L
TRACE=1 $T 3 0 1 0 0 25 2 0 1 0 0 1 >> $L 2>&1
echo "== E zh self-loop control: 3F5+S2+B(3)zh+25cyc mode1 ==" >> $L
$E 3 0 0 1 0 25 0 0 0 1 3 1 >> $L 2>&1
echo "== F zp3 self-launch control: 3F5+S2+B(3)zp3+25cyc mode1 ==" >> $L
$E 3 0 0 1 0 25 0 0 0 2 3 1 >> $L 2>&1
echo "CONTROLS2 DONE" >> $L
