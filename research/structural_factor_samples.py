"""Search finite connected examples; results are not a general theorem."""
from pathlib import Path
import json
import random
from structural_factors import analyse, edge

rng = random.Random(2026100801)
rows = []
for n in (12, 14, 16, 18):
    for sample in range(5):
        first = {edge(i, (i + 1) % n) for i in range(n)}
        while True:
            order = list(range(n))
            rng.shuffle(order)
            second = {edge(order[i], order[(i + 1) % n]) for i in range(n)}
            if not first & second:
                break
        row = analyse(n, sorted(first | second))
        rows.append(row)
        print(n, sample, row['count'], row['minimum'], row['maximum'], flush=True)
        Path(__file__).with_suffix('.json').write_text(
            json.dumps(rows, indent=2), encoding='utf-8')
