#!/usr/bin/env python3
"""P1400 construction using exact integers.
Usage: echo '3 10' | python code/vieta_construct.py
       python code/vieta_construct.py --verify
The verification covers every allowed k with n=1000; smaller n uses a prefix.
"""
from collections import deque
from pathlib import Path
import sys


def construct(k: int, count: int):
    if not (2 <= k <= 1000 and 1 <= count <= 1000):
        raise ValueError('This implementation is verified for the original bounds.')
    queue = deque([(1, k, k * (k + 1), 0)])
    used = set()
    result = []
    nodes = depth_max = digits_max = 0
    while len(result) < count:
        x, y, z, depth = queue.popleft()
        nodes += 1
        assert 0 < x < y < z
        if x not in used and y not in used and z not in used:
            assert x*x + y*y + z*z == k*(x*y + y*z + x*z) + 1
            assert z < 10**100
            used.update((x, y, z))
            result.append((x, y, z))
            depth_max = max(depth_max, depth)
            digits_max = max(digits_max, len(str(z)))
        # Expand even when the parent could not be selected.
        queue.append((y, z, k*(y+z)-x, depth+1))
        queue.append((x, z, k*(x+z)-y, depth+1))
    assert len(used) == 3*count
    return result, (nodes, depth_max, digits_max)


def verify():
    rows = []
    for k in range(2, 1001):
        _, stats = construct(k, 1000)
        rows.append((k, *stats))
    dest = Path(__file__).resolve().parent.parent / 'validation/vieta_full_range.csv'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text('k,nodes,depth,max_digits\n' + '\n'.join(','.join(map(str, r)) for r in rows) + '\n')
    print('PASS: all k=2..1000, n=1000; maxima:',
          *[max(row[i] for row in rows) for i in range(1, 4)])


if __name__ == '__main__':
    if '--verify' in sys.argv:
        verify()
    else:
        k, count = map(int, sys.stdin.read().split())
        result, _ = construct(k, count)
        for row in result:
            print(*row)
