# Bernoulli certificate for the prime 23

`BealRegular/TwentyThreeBernoulli.lean` isolates the finite arithmetic part of
Kummer's Bernoulli criterion.  It computes the canonical reduced rational
values and numerators

| index | Bernoulli number | reduced numerator | residue mod 23 |
|---:|---:|---:|---:|
| 2 | `1/6` | `1` | `1` |
| 4 | `-1/30` | `-1` | `22` |
| 6 | `1/42` | `1` | `1` |
| 8 | `-1/30` | `-1` | `22` |
| 10 | `5/66` | `5` | `5` |
| 12 | `-691/2730` | `-691` | `22` |
| 14 | `7/6` | `7` | `7` |
| 16 | `-3617/510` | `-3617` | `17` |
| 18 | `43867/798` | `43867` | `6` |
| 20 | `-174611/330` | `-174611` | `5` |

Thus `23` divides none of the reduced numerators of
`B_2, B_4, ..., B_20`.

The repository does not currently contain a formal proof of Kummer's theorem
identifying this numerator condition with regularity of a prime.  The Lean
endpoint therefore accepts the needed implication as an ordinary theorem
parameter.  With that parameter, the checked finite certificate gives
`IsRegularPrime 23`, and the existing `flt_regular` theorem then gives
`FermatLastTheoremFor 23`.  The parameter is visible in both theorem
statements; it is not installed as an axiom or typeclass instance.
