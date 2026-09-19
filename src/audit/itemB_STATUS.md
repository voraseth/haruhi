# itemB_STATUS — COMPLETE
T-n6-auditB, Algorithm 2 rejection rules R1-R14. All 14 classified, none (c).
- itemB_audit.md: classification table + summary + control results.
- itemB_proofs.md: self-contained reproduced proofs (raw defs -> R1-R14),
  dependency DAG (acyclic), direction-soundness audit of the scanner's
  substitutions (SH:=hits, ST:=cnl, X4h:=X4, slack weakening).
- checks/itemB_controls.py + logs/itemB_controls.log: machine control —
  verified 872 + all 96 verified 873s pass all 14 rules at their own lengths
  (97 objects, 0 rejections). Runtime ~2 CPU-min.
Sources: approaches/n6/proof6.md §§1-9, approaches/n6-871/proof871.md §§1-5,
PAPER-n6-872.tex Appendix A.2, scan871.py / lib6.py / chain6.c / chains871.c.
