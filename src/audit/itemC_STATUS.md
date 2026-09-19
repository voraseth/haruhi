# itemC_STATUS.md — T-n6-auditC — COMPLETE
All four work items classified; no undischarged (c).
- C2 (X4h): CONSERVATIVE RELAXATION — PROVED (Lemma C2.1, itemC_proofs.md;
  checker checks/itemC_x4h_check.py PASS, 3.3 s).
- Lemma 5.4 GROUPS: (a) PROVED.  Lemma 5.2 PARETOS: (a) PROVED.
- Lemma 5.3 CHAINRUN: (b) FINITE-CHECK, sufficiency argument supplied & audited.
- Controls: 97/97 (verified 872 + 96 verified 873s) pass every certified clause;
  X4h checker survivor sets identical under both semantics, both control cells
  alive.  Details: itemC_audit.md, itemC_proofs.md, logs/itemC_*.log.
Paper fixes required (presentation, not mathematics): (1) replace "set
X4h = X4" in Algorithm 2 by "bound X4h <= X4" with Fact C2.0; (2) replace the
one-sentence gloss at PAPER line 571 by the proofs of proof871.md sections 3-5
(or inline them), including the gS sufficiency argument recorded here.
