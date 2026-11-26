#!/usr/bin/env -S python3 -I
"""Pilot 1's draw (Step 24): the Step 19 manifest's 61 targets, in its order
(population.tsv: row, contest, contract), shuffled with random.Random(0);
the first five are the pilot's targets.

    python3 -I eval/pilot/draw.py eval/pilot/population.tsv
"""

import random
import sys

rows = [line.rstrip("\n").split("\t") for line in open(sys.argv[1]) if line.strip()]
order = list(range(len(rows)))
random.Random(0).shuffle(order)
print(f"{len(rows)} targets, {len({r[1] for r in rows})} contests")
for i in order[:5]:
    print("\t".join(rows[i]))
