#!/opt/homebrew/bin/python3.11
"""Discover a generator for the cube of one prime above 2 in Q(zeta_23).

This script is a witness finder, not part of the trusted proof.  The emitted
polynomial identities are checked independently by a BigInt Node script and
then by Lean's kernel.
"""

from itertools import product
import json

import sympy as sp
from sympy.matrices.normalforms import hermite_normal_form
from sympy.polys.matrices import DomainMatrix


X = sp.symbols("X")
DEGREE = 22
PHI = sp.Poly(sum(X**i for i in range(23)), X, domain=sp.ZZ)
Q = 2


def reduced(poly):
    return sp.rem(sp.Poly(poly, X, domain=sp.ZZ), PHI)


def vector(poly):
    poly = reduced(poly)
    return [int(poly.nth(i)) for i in range(DEGREE)]


def polynomial(values):
    return sp.Poly(sum(value * X**i for i, value in enumerate(values)), X, domain=sp.ZZ)


def exact_quotient(numerator, denominator):
    quotient, remainder = sp.div(numerator, denominator, domain=sp.ZZ)
    assert remainder.is_zero
    return quotient


def coeffs(poly):
    if poly.is_zero:
        return []
    return [str(int(poly.nth(i))) for i in range(poly.degree() + 1)]


factors = sp.factor_list(PHI.as_expr(), modulus=Q)[1]
F = sp.Poly(factors[0][0], X, domain=sp.ZZ)
assert F.degree() == 11

monomials = [sp.Poly(Q**3, X), Q**2 * F, Q * F**2, F**3]
columns = []
for monomial in monomials:
    for exponent in range(DEGREE):
        columns.append(vector(monomial * X**exponent))

A = sp.Matrix(DEGREE, len(columns), lambda i, j: columns[j][i])
H = hermite_normal_form(A)
assert H.shape == (DEGREE, DEGREE)
assert abs(int(H.det())) == Q ** 33

# H's columns are a Z-basis of the ideal.  SymPy's LLL implementation expects
# basis vectors in rows.
B = DomainMatrix.from_Matrix(H.transpose()).lll(delta=sp.Rational(99, 100)).to_Matrix()
target_norm = Q ** 33


def field_norm(values):
    return abs(int(sp.resultant(PHI.as_expr(), polynomial(values).as_expr(), X)))


candidates = [list(map(int, B.row(i))) for i in range(DEGREE)]
generator = next((candidate for candidate in candidates if field_norm(candidate) == target_norm), None)

if generator is None:
    # Principal generators are normally visible in the reduced basis.  Keep a
    # deterministic small-combination fallback so this remains reproducible
    # across harmless LLL implementation changes.
    short = candidates[:12]
    for support in range(2, 5):
        for indices in product(range(len(short)), repeat=support):
            if tuple(sorted(indices)) != indices:
                continue
            for signs in product([-1, 1], repeat=support):
                candidate = [
                    sum(signs[j] * short[indices[j]][i] for j in range(support))
                    for i in range(DEGREE)
                ]
                if field_norm(candidate) == target_norm:
                    generator = candidate
                    break
            if generator is not None:
                break
        if generator is not None:
            break

if generator is None:
    raise RuntimeError("LLL search did not find a norm-2^33 ideal generator")

G = polynomial(generator)

# Solve G*Qi = q^(3-i)*F^i in the quotient Z[X]/(Phi).  Integrality of
# each solution is part of the witness check below.
MG = sp.Matrix(DEGREE, DEGREE, lambda i, j: vector(G * X**j)[i])
quotients = []
remainders = []
for monomial in monomials:
    solution = MG.inv() * sp.Matrix(vector(monomial))
    assert all(value.q == 1 for value in solution)
    quotient = polynomial([int(value) for value in solution])
    difference = monomial - G * quotient
    remainder = exact_quotient(difference, PHI)
    quotients.append(quotient)
    remainders.append(remainder)
    assert monomial == G * quotient + PHI * remainder

# Recover an explicit reverse-containment expression by successive division
# in the 2-adic filtration (2,F)^3.  Modulo 2, Phi=F*Fbar; on the Fbar
# component every power of F is invertible.
F2 = sp.Poly(F.as_expr(), X, modulus=2)
Fbar2 = next(
    sp.Poly(factor, X, modulus=2)
    for factor, _ in factors
    if sp.Poly(factor, X, modulus=2) != F2
)


def lift_multiple_mod_two(value, power):
    value2 = sp.Poly(value.as_expr(), X, modulus=2)
    assert value2.rem(F2).is_zero
    fpow2 = sp.Poly(F2.as_expr() ** power, X, modulus=2)
    inverse = sp.invert(fpow2, Fbar2)
    result2 = sp.Poly(value2.rem(Fbar2).as_expr() * inverse, X, modulus=2).rem(Fbar2)
    return polynomial([int(result2.nth(i)) % 2 for i in range(DEGREE)])


current = G
reverse = {}
for power in [3, 2, 1]:
    coefficient = lift_multiple_mod_two(current, power)
    reverse[power] = coefficient
    even_remainder = reduced(current - F**power * coefficient)
    even_vector = vector(even_remainder)
    assert all(value % 2 == 0 for value in even_vector)
    current = polynomial([value // 2 for value in even_vector])

C0 = current
C1 = reverse[1]
C2 = reverse[2]
C3 = reverse[3]
combination = C0 * Q**3 + C1 * (Q**2 * F) + C2 * (Q * F**2) + C3 * F**3
R4 = exact_quotient(G - combination, PHI)
assert G == combination + PHI * R4

certificate = {
    "p": 23,
    "q": Q,
    "residue_degree": 11,
    "ideal_norm": Q**11,
    "cube_norm": target_norm,
    "Phi": coeffs(PHI),
    "F": coeffs(F),
    "G": coeffs(G),
    "Q0": coeffs(quotients[0]),
    "Q1": coeffs(quotients[1]),
    "Q2": coeffs(quotients[2]),
    "Q3": coeffs(quotients[3]),
    "R0": coeffs(remainders[0]),
    "R1": coeffs(remainders[1]),
    "R2": coeffs(remainders[2]),
    "R3": coeffs(remainders[3]),
    "C0": coeffs(C0),
    "C1": coeffs(C1),
    "C2": coeffs(C2),
    "C3": coeffs(C3),
    "R4": coeffs(R4),
}

print(json.dumps(certificate, separators=(",", ":")))
