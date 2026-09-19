#!/bin/zsh
# The 8 sub-configs of the pinned (20,0,0) e=9 census (D-ledger + class budget:
# nS=2 => a+b+s2 = 8+n4 ; nS=3 => a+b+c+s2 = 13+n4, only (3,3,3),s2=4).
# argv: n5 n4 n3 n2 n1 ncyc m2spec cap
R=./realize
C=4000000000
echo "job1 n5=16 shorts(3,3) s2=2";  $R 16 0 2 0 0 8 11 $C
echo "job2 n5=16 shorts(3,2) s2=3";  $R 16 0 1 1 0 8 12,21 $C
echo "job3 n5=16 shorts(3,1) s2=4";  $R 16 0 1 0 1 8 13,31,22 $C
echo "job4 n5=16 shorts(2,2) s2=4";  $R 16 0 0 2 0 8 13,31,22 $C
echo "job5 n4=1 shorts(3,3) s2=3";   $R 15 1 2 0 0 8 12,21 $C
echo "job6 n4=1 shorts(3,2) s2=4";   $R 15 1 1 1 0 8 13,31,22 $C
echo "job7 n4=2 shorts(3,3) s2=4";   $R 14 2 2 0 0 8 13,31,22 $C
echo "job8 n5=15 shorts(3,3,3) s2=4";$R 15 0 3 0 0 8 13,31,22 $C
