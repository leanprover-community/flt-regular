import json

BOUND = 13254
K.<z> = CyclotomicField(17)
R.<X> = PolynomialRing(ZZ)
phi = sum(X^i for i in range(17))

def coeffs(poly):
    if poly == 0:
        return []
    # Decimal strings preserve arbitrarily large coefficients through JSON.
    return [str(poly[i]) for i in range(poly.degree() + 1)]

def integral_poly(element):
    values = list(K(element))
    assert all(value.denominator() == 1 for value in values)
    return R([ZZ(value) for value in values])

certificates = []
for p in prime_range(BOUND + 1):
    if p == 17:
        continue
    order = Mod(p, 17).multiplicative_order()
    if p^order > BOUND:
        continue

    ideal = K.primes_above(p)[0]
    _, ideal_polynomial_element = ideal.gens_two()
    P = integral_poly(ideal_polynomial_element)
    assert P.is_monic()
    assert P.degree() == order

    generator = ideal.gens_reduced()[0]
    G = integral_poly(generator)
    assert abs(generator.norm()) == p^order

    Qp = integral_poly(K(p) / generator)
    difference_p = R(p) - G * Qp
    Rp, remainder_p = difference_p.quo_rem(phi)
    assert remainder_p == 0

    QP = integral_poly(K(ideal_polynomial_element) / generator)
    difference_P = P - G * QP
    RP, remainder_P = difference_P.quo_rem(phi)
    assert remainder_P == 0

    C1, remainder_G = G.quo_rem(P)
    assert all(coefficient % p == 0 for coefficient in remainder_G)
    C2 = R([coefficient // p for coefficient in remainder_G])
    assert G == C1 * P + C2 * p

    quotient_phi, remainder_phi = phi.quo_rem(P)
    assert all(coefficient % p == 0 for coefficient in remainder_phi)
    A = R([coefficient // p for coefficient in remainder_phi])
    assert P * quotient_phi + p * A == phi

    certificates.append({
        "p": int(p),
        "order": int(order),
        "P": coeffs(P),
        "Q": coeffs(quotient_phi),
        "A": coeffs(A),
        "G": coeffs(G),
        "Qp": coeffs(Qp),
        "Rp": coeffs(Rp),
        "QP": coeffs(QP),
        "RP": coeffs(RP),
        "C1": coeffs(C1),
        "C2": coeffs(C2),
    })

print(json.dumps({
    "bound": int(BOUND),
    "class_number": int(K.class_number()),
    "certificates": certificates,
}, separators=(",", ":")))
