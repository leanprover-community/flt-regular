#!/opt/homebrew/bin/python3.11
"""Reproduce a generator for the cube of one prime above 3 in Q(zeta_23).

This script is a witness finder, not part of the trusted proof.  The emitted
polynomial identities are checked independently by a BigInt Node script and
then by Lean's kernel.

The factor and final generator are pinned so a harmless change in SymPy's
factor or LLL ordering cannot silently rewrite the checked certificate.  The
script still recomputes the ideal lattice, checks that the pinned generator is
in it with the expected norm, and independently derives every quotient.
"""

from itertools import product
import json

import sympy as sp
from sympy.matrices.normalforms import hermite_normal_form
from sympy.polys.matrices import DomainMatrix


X = sp.symbols("X")
DEGREE = 22
PHI = sp.Poly(sum(X**i for i in range(23)), X, domain=sp.ZZ)
Q = 3

EXPECTED_F = sp.Poly(
    X**11 - X**8 - X**6 + X**4 + X**3 - X**2 - X - 1,
    X,
    domain=sp.ZZ,
)
EXPECTED_GENERATOR = [
    -2, 0, -2, -2, -2, -2, 1, 0, 0, 0, 0,
    -2, 0, -2, 0, 0, -2, -2, 0, 0, -2, -2,
]


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
assert len(factors) == 2
assert all(exponent == 1 for _, exponent in factors)
factor_polys = [sp.Poly(factor, X, modulus=Q) for factor, _ in factors]
Fq = sp.Poly(EXPECTED_F.as_expr(), X, modulus=Q)
assert Fq in factor_polys
assert all(factor.degree() == 11 for factor in factor_polys)
F = EXPECTED_F

monomials = [sp.Poly(Q**3, X), Q**2 * F, Q * F**2, F**3]
columns = []
for monomial in monomials:
    for exponent in range(DEGREE):
        columns.append(vector(monomial * X**exponent))

A = sp.Matrix(DEGREE, len(columns), lambda i, j: columns[j][i])
H = hermite_normal_form(A)
assert H.shape == (DEGREE, DEGREE)
assert abs(int(H.det())) == Q**33


def field_norm(values):
    return abs(int(sp.resultant(PHI.as_expr(), polynomial(values).as_expr(), X)))


target_norm = Q**33

# Check the pinned output against the recomputed ideal lattice, rather than
# trusting the discovery run which originally produced it.
coordinates = H.inv() * sp.Matrix(EXPECTED_GENERATOR)
assert all(value.q == 1 for value in coordinates)
assert H * coordinates == sp.Matrix(EXPECTED_GENERATOR)
assert field_norm(EXPECTED_GENERATOR) == target_norm

# SymPy's LLL implementation expects basis vectors in rows.  Keeping this
# search makes the original discovery reproducible, while the pinned output
# above keeps the emitted certificate stable if an equally valid short basis
# is ordered differently in another SymPy release.
B = DomainMatrix.from_Matrix(H.transpose()).lll(delta=sp.Rational(99, 100)).to_Matrix()
candidates = [list(map(int, B.row(i))) for i in range(DEGREE)]
discovered = next((candidate for candidate in candidates if field_norm(candidate) == target_norm), None)

if discovered is None:
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
                    discovered = candidate
                    break
            if discovered is not None:
                break
        if discovered is not None:
            break

if discovered is None:
    raise RuntimeError("LLL search did not find a norm-3^33 ideal generator")

G = polynomial(EXPECTED_GENERATOR)

# Solve G*Qi = q^(3-i)*F^i in Z[X]/(Phi).  Integrality of each solution is
# checked before the exact integer-polynomial identities are emitted.
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
# in the q-adic filtration (q,F)^3.  Modulo q, Phi=F*Fbar; on the Fbar
# component every power of F is invertible.
Fbarq = next(factor for factor in factor_polys if factor != Fq)


def lift_multiple_mod_q(value, power):
    valueq = sp.Poly(value.as_expr(), X, modulus=Q)
    assert valueq.rem(Fq).is_zero
    fpowq = sp.Poly(Fq.as_expr() ** power, X, modulus=Q)
    inverse = sp.invert(fpowq, Fbarq)
    resultq = sp.Poly(valueq.rem(Fbarq).as_expr() * inverse, X, modulus=Q).rem(Fbarq)
    return polynomial([int(resultq.nth(i)) % Q for i in range(DEGREE)])


current = G
reverse = {}
for power in [3, 2, 1]:
    coefficient = lift_multiple_mod_q(current, power)
    reverse[power] = coefficient
    q_multiple = reduced(current - F**power * coefficient)
    q_vector = vector(q_multiple)
    assert all(value % Q == 0 for value in q_vector)
    current = polynomial([value // Q for value in q_vector])

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
