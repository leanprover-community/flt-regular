#!/usr/bin/env node

// Verify the exact finite arithmetic behind the proposed relative-class-number
// route for Q(zeta_23). This script is research evidence only: it does not
// prove the relative class-number formula, a PID theorem for the maximal real
// subfield, or any Lean declaration.

const assert = (condition, message) => {
  if (!condition) throw new Error(message);
};

const abs = (value) => (value < 0n ? -value : value);

const trimPolynomial = (coefficients) => {
  const result = coefficients.slice();
  while (result.length > 0 && result.at(-1) === 0n) result.pop();
  return result;
};

// Fraction-free Gaussian elimination. All divisions in the Bareiss algorithm
// are exact; checking that exactness makes the determinant computation itself
// independently auditable.
const determinantBareiss = (input) => {
  const size = input.length;
  assert(input.every((row) => row.length === size), "determinant matrix is not square");
  if (size === 0) return 1n;
  if (size === 1) return input[0][0];

  const matrix = input.map((row) => row.slice());
  let sign = 1n;
  let previousPivot = 1n;

  for (let pivotIndex = 0; pivotIndex < size - 1; pivotIndex += 1) {
    let pivotRow = pivotIndex;
    while (pivotRow < size && matrix[pivotRow][pivotIndex] === 0n) pivotRow += 1;
    if (pivotRow === size) return 0n;

    if (pivotRow !== pivotIndex) {
      [matrix[pivotIndex], matrix[pivotRow]] = [matrix[pivotRow], matrix[pivotIndex]];
      sign = -sign;
    }

    const pivot = matrix[pivotIndex][pivotIndex];
    for (let row = pivotIndex + 1; row < size; row += 1) {
      for (let column = pivotIndex + 1; column < size; column += 1) {
        const numerator =
          matrix[row][column] * pivot -
          matrix[row][pivotIndex] * matrix[pivotIndex][column];
        assert(
          numerator % previousPivot === 0n,
          `non-exact Bareiss division at (${row}, ${column})`,
        );
        matrix[row][column] = numerator / previousPivot;
      }
      matrix[row][pivotIndex] = 0n;
    }
    previousPivot = pivot;
  }

  return sign * matrix[size - 1][size - 1];
};

// Coefficients are stored in ascending order. The row ordering below is the
// standard Sylvester convention used for Res(left, right).
const resultant = (leftInput, rightInput) => {
  const left = trimPolynomial(leftInput);
  const right = trimPolynomial(rightInput);
  assert(left.length > 0 && right.length > 0, "resultant of the zero polynomial");

  const leftDegree = left.length - 1;
  const rightDegree = right.length - 1;
  const size = leftDegree + rightDegree;
  const matrix = Array.from({ length: size }, () => Array(size).fill(0n));

  for (let row = 0; row < rightDegree; row += 1) {
    for (let index = 0; index <= leftDegree; index += 1) {
      matrix[row][row + index] = left[leftDegree - index];
    }
  }
  for (let row = 0; row < leftDegree; row += 1) {
    for (let index = 0; index <= rightDegree; index += 1) {
      matrix[rightDegree + row][row + index] = right[rightDegree - index];
    }
  }

  return determinantBareiss(matrix);
};

const derivative = (polynomial) =>
  polynomial.slice(1).map((coefficient, index) => BigInt(index + 1) * coefficient);

const modularPower = (base, exponent, modulus) => {
  let result = 1n;
  let power = base % modulus;
  let remaining = exponent;
  while (remaining > 0n) {
    if (remaining % 2n === 1n) result = (result * power) % modulus;
    power = (power * power) % modulus;
    remaining /= 2n;
  }
  return result;
};

const multiplicativeOrder = (value, modulus) => {
  let power = value % modulus;
  for (let order = 1; order < Number(modulus); order += 1) {
    if (power === 1n) return order;
    power = (power * value) % modulus;
  }
  throw new Error(`${value} is not a unit modulo ${modulus}`);
};

const factorial = (value) => {
  let result = 1n;
  for (let factor = 2n; factor <= value; factor += 1n) result *= factor;
  return result;
};

const isPrime = (value) => {
  if (value < 2) return false;
  for (let divisor = 2; divisor * divisor <= value; divisor += 1) {
    if (value % divisor === 0) return false;
  }
  return true;
};

// In the maximal real subfield, residue degree is the order of q in
// (Z/23Z)^x/{+1,-1}: the first exponent for which q^f is +1 or -1 mod 23.
const realResidueDegree = (prime) => {
  const modulus = 23;
  const residue = prime % modulus;
  let power = residue;
  for (let degree = 1; degree <= 11; degree += 1) {
    if (power === 1 || power === modulus - 1) return degree;
    power = (power * residue) % modulus;
  }
  throw new Error(`failed to find the real residue degree of ${prime}`);
};

const powerAtMost = (base, exponent, bound) => {
  let value = 1n;
  for (let index = 0; index < exponent; index += 1) {
    value *= BigInt(base);
    if (value > bound) return false;
  }
  return true;
};

// Laurent-polynomial helpers used to derive the normalized real-subfield
// polynomial from a = -(zeta + zeta^-1). A Laurent polynomial is a Map from
// integer exponents to BigInt coefficients.
const addLaurent = (left, right) => {
  const result = new Map(left);
  for (const [exponent, coefficient] of right) {
    result.set(exponent, (result.get(exponent) ?? 0n) + coefficient);
  }
  for (const [exponent, coefficient] of result) {
    if (coefficient === 0n) result.delete(exponent);
  }
  return result;
};

const multiplyLaurent = (left, right) => {
  const result = new Map();
  for (const [leftExponent, leftCoefficient] of left) {
    for (const [rightExponent, rightCoefficient] of right) {
      const exponent = leftExponent + rightExponent;
      result.set(
        exponent,
        (result.get(exponent) ?? 0n) + leftCoefficient * rightCoefficient,
      );
    }
  }
  return result;
};

const scaleLaurent = (polynomial, scalar) =>
  new Map([...polynomial].map(([exponent, coefficient]) => [exponent, scalar * coefficient]));

const conductor = 23n;
const primitiveRoot = 5n;
assert(
  multiplicativeOrder(primitiveRoot, conductor) === 22,
  "5 is not a primitive root modulo 23",
);

// For odd characters chi_k with chi_k(5) a root of T^11 + 1, the finite
// character sums are encoded by A(T) below.
const characterSumPolynomial = [];
for (let exponent = 0n; exponent < 22n; exponent += 1n) {
  characterSumPolynomial.push(modularPower(primitiveRoot, exponent, conductor));
}
const expectedCharacterSumPolynomial = [
  1n, 5n, 2n, 10n, 4n, 20n, 8n, 17n, 16n, 11n, 9n,
  22n, 18n, 21n, 13n, 19n, 3n, 15n, 6n, 7n, 12n, 14n,
];
assert(
  characterSumPolynomial.every(
    (coefficient, index) => coefficient === expectedCharacterSumPolynomial[index],
  ),
  "unexpected powers of 5 modulo 23",
);

const oddCharacterPolynomial = [1n, ...Array(10).fill(0n), 1n]; // T^11 + 1
const oddCharacterResultant = resultant(oddCharacterPolynomial, characterSumPolynomial);
const relativeDenominator = 46n ** 10n;
const expectedOddCharacterResultant = -3n * relativeDenominator;
assert(
  oddCharacterResultant === expectedOddCharacterResultant,
  `unexpected odd-character resultant ${oddCharacterResultant}`,
);

// This is the LMFDB-normalized polynomial for a = -(zeta + zeta^-1).
// The Laurent identity checked below is
//   X^11 f(-(X + X^-1)) = -Phi_23(X).
const realSubfieldPolynomial = [
  1n, -6n, -15n, 35n, 35n, -56n, -28n, 36n, 9n, -10n, -1n, 1n,
];
const minusXPlusInverse = new Map([
  [-1, -1n],
  [1, -1n],
]);
let laurentPower = new Map([[0, 1n]]);
let evaluatedRealPolynomial = new Map();
for (const coefficient of realSubfieldPolynomial) {
  evaluatedRealPolynomial = addLaurent(
    evaluatedRealPolynomial,
    scaleLaurent(laurentPower, coefficient),
  );
  laurentPower = multiplyLaurent(laurentPower, minusXPlusInverse);
}
const shiftedRealPolynomial = new Map(
  [...evaluatedRealPolynomial].map(([exponent, coefficient]) => [exponent + 11, coefficient]),
);
assert(shiftedRealPolynomial.size === 23, "real-subfield identity has unexpected support");
for (let exponent = 0; exponent <= 22; exponent += 1) {
  assert(
    shiftedRealPolynomial.get(exponent) === -1n,
    `real-subfield identity failed at X^${exponent}`,
  );
}

const realPolynomialDegree = realSubfieldPolynomial.length - 1;
const realPolynomialDerivative = derivative(realSubfieldPolynomial);
const realPolynomialResultant = resultant(realSubfieldPolynomial, realPolynomialDerivative);
const discriminantSign = (realPolynomialDegree * (realPolynomialDegree - 1)) / 2 % 2 === 0
  ? 1n
  : -1n;
const realSubfieldDiscriminant = discriminantSign * realPolynomialResultant;
const expectedRealSubfieldDiscriminant = conductor ** 10n;
assert(
  realSubfieldDiscriminant === expectedRealSubfieldDiscriminant,
  `unexpected real-subfield discriminant ${realSubfieldDiscriminant}`,
);

// The totally real Minkowski bound is exactly
//   11! / 11^11 * sqrt(23^10) = 11! * 23^5 / 11^11.
const realMinkowskiNumerator = factorial(11n) * conductor ** 5n;
const realMinkowskiDenominator = 11n ** 11n;
const realMinkowskiFloor = realMinkowskiNumerator / realMinkowskiDenominator;
assert(realMinkowskiFloor === 900n, `unexpected real Minkowski floor ${realMinkowskiFloor}`);
assert(
  900n * realMinkowskiDenominator < realMinkowskiNumerator &&
    realMinkowskiNumerator < 901n * realMinkowskiDenominator,
  "exact rational interval does not certify the real Minkowski floor",
);

const relevantUnramifiedPrimes = [];
for (let prime = 2; prime <= Number(realMinkowskiFloor); prime += 1) {
  if (!isPrime(prime) || prime === Number(conductor)) continue;
  const residueDegree = realResidueDegree(prime);
  if (powerAtMost(prime, residueDegree, realMinkowskiFloor)) {
    relevantUnramifiedPrimes.push(prime);
  }
}
const expectedRelevantUnramifiedPrimes = [
  47, 137, 139, 229, 277, 367, 461, 599, 643, 691, 827, 829,
];
assert(
  JSON.stringify(relevantUnramifiedPrimes) ===
    JSON.stringify(expectedRelevantUnramifiedPrimes),
  `unexpected real-subfield prime list ${JSON.stringify(relevantUnramifiedPrimes)}`,
);

console.log(JSON.stringify({
  warning: "finite arithmetic only; the relative class-number formula and real-subfield PID proof are missing",
  conductor: Number(conductor),
  primitiveRoot: Number(primitiveRoot),
  characterSumPolynomialAscending: characterSumPolynomial.map(String),
  oddCharacterResultant: oddCharacterResultant.toString(),
  expectedResultantFactorization: `-3 * 46^10`,
  resultantQuotientAbs: (abs(oddCharacterResultant) / relativeDenominator).toString(),
  realSubfield: {
    generator: "-(zeta_23 + zeta_23^-1)",
    polynomialAscending: realSubfieldPolynomial.map(String),
    discriminant: realSubfieldDiscriminant.toString(),
    minkowskiBoundRational: {
      numerator: realMinkowskiNumerator.toString(),
      denominator: realMinkowskiDenominator.toString(),
      floor: realMinkowskiFloor.toString(),
    },
    ramifiedPrime: Number(conductor),
    relevantUnramifiedPrimes,
  },
}, null, 2));
