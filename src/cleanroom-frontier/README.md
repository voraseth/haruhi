# Clean-room frontier enumerator (conformance row C12): discharged

The second, independently written enumerator for the chain-capacity
tables of Appendix B.  Row C12 of the conformance ledger (paper,
Section 8) is discharged by what is in this directory.

## Provenance

`sweep_decide.c` was written against the paper's printed specification
alone: Definition F, Lemma 4.4 (the chain-capacity lemma), and the
abstract-chain domain of Appendix C.2.12.  Its author read neither
`../frontier/chains871.c` nor any other enumerator in this repository.
It shares no code with the original.

## What it settles

Row C12 was the last open obligation, and it is one number.  The census
of Algorithm G consumes a certified cap of **25 at cost 19**; rows 19
and 20 of the coarse table supply it redundantly, either one sufficing
by monotonicity of g in the cost.  That value is genuinely load-bearing:
the classification and Lemma 6.7 survive replacing both rows by the
universal bound `4 - 2a - 2b + 2c`, but the census does not, admitting
10 further configurations and 22 further instances that were never
searched.  So the value had to be certified a second time rather than
argued away.

Result (`logs/run_c20.out`), by complete exhaustion over the
abstract-chain domain, 16,571,498,239 nodes:

    cost 19  ->  g(19,.) = (25, 25, 25, 24)
    cost 20  ->  g(20,.) = (25, 25, 25, 25)

in the endpoint-type order (0,0), (1,0), (0,1), (1,1).  Every one of the
21 rows, costs 0 through 20, agrees entry for entry with Table 5 of the
paper.

Three further checks:

- **Pruning-free.** `logs/run_c20_nogate.out` is the same run with the
  `r <= 4` run-count gate removed. The table is identical and so is the
  node count, 16,571,498,239, so the gate never cut a live branch. Some
  witness chains differ, since a different attaining chain is reached
  first; the values do not.
- **C6-A re-confirmed.** `c6a_decide.c` independently re-derives the
  run bound over all 720 heads: max 4 paths per maximal {4,5}-run, at
  most 2 of length 4, and 0 interior length-4 occurrences.
- **Witnesses re-verified.** `check_witness.py` re-checks each printed
  attaining chain from the raw definitions (class-disjointness, the
  rho-advance, exact-cost-3 hops, the claimed block count). All eight
  cost-19 and cost-20 witnesses pass, in both runs.

## Running it

Everything runs from inside this directory. No absolute paths.

    cc -O2 -pthread -o sweep_decide sweep_decide.c
    cc -O2 -o c6a_decide c6a_decide.c

Smoke test, costs 0 to 12, a few seconds:

    ./sweep_decide -c12 -t4

Rows 0 through 12 of the output table should match the paper's Table 5
exactly, ending `12 & 19 & 17 & 17 & 16`.

The full run reproducing `logs/run_c20.out` (about 2.5 minutes on 10
threads, and the same again for the ungated run):

    ./sweep_decide -c20 -t10 -s4          > run_c20.out
    ./sweep_decide -c20 -t10 -s4 -g0      > run_c20_nogate.out

Flags: `-cN` maximum cost, `-tN` threads, `-sN` parallel split depth,
`-g0` disables the run-count gate. Then:

    python3 check_witness.py run_c20.out
    ./c6a_decide

Expected: `ALL WITNESSES VALID`, and
`all 720 heads: max paths=4 max len4=2 interior-4 occurrences=0`.

A note on node counts. The paper fixes no unit of "node", so the count
above is reproducible against *this* program and is not an
implementation-independent quantity. The table's **values** are the
invariant, and those are what two written enumerators now agree on. The
same caveat applies to the node figures quoted for the original
enumerator in the paper's reproduction record.

## Files

| path | what |
|---|---|
| `sweep_decide.c` | the enumerator over the abstract-chain domain |
| `c6a_decide.c` | independent re-derivation of the run bound C6-A |
| `check_witness.py` | re-verifies a printed attaining chain from the definitions |
| `logs/run_c20.out` | the full table to cost 20, with attaining witnesses |
| `logs/run_c20_nogate.out` | the same with the run-count gate disabled |

See also `../cleanroom-loop/`, the clean-room engine that discharged
row C11. The two directories are independent of each other and of the
original implementations.

Note: repeat runs of the same command may also report different attaining
chains for some cells (thread scheduling decides which maximum-attaining
chain is recorded first); the table values and node count are invariant,
and every reported chain passes check_witness.py.
