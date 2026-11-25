"""Check the sharp pointwise bound on every labeled connected graph of orders 2..6."""
from fractions import Fraction
from itertools import combinations
from math import isqrt

SCALE = 10**8

def upper_edge_weight(product):
    # floor(sqrt(product)*SCALE) <= sqrt(product)*SCALE.
    return Fraction(SCALE, isqrt(product*SCALE*SCALE))

def check_order(n):
    vertices = range(n)
    pairs = list(combinations(vertices, 2))
    weights = {s:upper_edge_weight(s) for s in range(1,n*n)}
    tested = exact_equalities = 0
    for mask in range(1<<len(pairs)):
        edges = [edge for i,edge in enumerate(pairs) if mask>>i&1]
        if len(edges)<n-1: continue
        adj = [set() for v in vertices]
        for u,v in edges: adj[u].add(v); adj[v].add(u)
        reached, frontier = {0}, [0]
        while frontier:
            added = adj[frontier.pop()]-reached
            frontier.extend(added); reached.update(added)
        if len(reached)!=n: continue
        degree = [len(row) for row in adj]
        upper_r = sum(weights[degree[u]*degree[v]] for u,v in edges)
        scores = [Fraction(2**d*(n-d),d) for d in degree]
        if 4*upper_r > 3*min(scores): raise ValueError((n, mask, upper_r, scores))
        if 4*upper_r == 3*min(scores):
            assert all(isqrt(degree[u]*degree[v])**2 == degree[u]*degree[v] for u,v in edges)
            exact_equalities += 1
        tested += 1
    print(f"n={n}: {tested} connected labeled graphs passed; {exact_equalities} exact pointwise ties")

if __name__=='__main__':
    for order in range(2,7): check_order(order)
