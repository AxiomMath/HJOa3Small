[![](logo.svg)](https://axiommath.ai/)

# Small cases of HJO at a = 3

This is a Lean formalization of small cases of HJO at a = 3.

## Main Results

* The sum-to-sum conjecture for b = 4, 5, 7, 8.
* The sum-to-sum conjecture for all b > 3 coprime to 3 at q = 1.
* The HJO conjecture for b = 4, 5, 7, 8, assuming Warnaar's Theorem 1.1.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on Axiom Math's repository [QSeriesLib](https://github.com/AxiomMath/QSeriesLib).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Comparator/Challenge.lean](Comparator/Challenge.lean). This file only depends on Mathlib and QSeriesLib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
