"""Finite low-type checks, not a proof of the full higher-order constructions.

OpenAI Codex, prompted by Andrew Bacon, 28 October 2026.
"""
from itertools import product


def powerset(xs):
    xs = tuple(xs)
    return tuple(frozenset(x for x, bit in zip(xs, bits) if bit)
                 for bits in product((False, True), repeat=len(xs)))


def check_transformation_model():
    X = (0, 1)
    M = tuple(product(X, repeat=len(X)))
    one, k = (0, 1), (0, 0)
    compose = lambda g, f: tuple(g[f[x]] for x in X)
    P = powerset(M)
    transport = lambda f, p: frozenset(g for g in M if compose(g, f) in p)
    # Check that the propositional transport really is an action.
    for f, g, p in product(M, M, P):
        assert transport(compose(g, f), p) == transport(g, transport(f, p))
    reachable = {f: frozenset(compose(g, f) for g in M) for f in M}
    box = lambda p: frozenset(f for f in M if reachable[f] <= p)
    diamond = lambda p: frozenset(f for f in M if reachable[f] & p)
    a = frozenset((one,))
    assert one in a and one not in box(diamond(a))  # B fails.
    for domain, act in [(X, lambda f, x: f[x]), (P, transport)]:
        H = {f: frozenset(act(f, x) for x in domain) for f in M}
        # For every original x, H(x) holds at every arrow (BF premise).
        assert all(act(f, x) in H[f] for f in M for x in domain)
        # At k, the target domain has an entity outside that image.
        assert set(domain) - H[k]
    assert a not in {transport(k, p) for p in P}
    assert transport(k, a) == transport(k, frozenset())
    # Every nonempty proposition has a singleton atom beneath it.
    for p in P:
        if p:
            atom = frozenset((next(iter(p)),))
            assert atom <= p
            assert all(q in (frozenset(), atom) for q in P if q <= atom)
    assert len(M) == 4 and len(P) == 16


def check_kripke_instances():
    W = frozenset((0, 1))
    R = {0: W, 1: frozenset((1,))}
    box = lambda p: frozenset(w for w in W if R[w] <= p)
    diamond = lambda p: frozenset(w for w in W if R[w] & p)
    p = frozenset((0,))
    assert 0 in p and 0 not in box(diamond(p))
    D = {0: ('a',), 1: ('a', 'b')}
    H = {'a': W, 'b': frozenset()}
    assert all(0 in box(H[x]) for x in D[0])
    universal = frozenset(w for w in W if all(w in H[x] for x in D[w]))
    assert 0 not in box(universal)
    assert all(H[x] == W for x in D[0])  # equal to top on current arguments
    assert any(H[x] != W for x in D[1])  # but not identical as properties


if __name__ == '__main__':
    check_transformation_model()
    check_kripke_instances()
    print('Bacon model witnesses: finite B/BF/equality/atomicity checks passed.')
