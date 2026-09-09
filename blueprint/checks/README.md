# Finite mathematical checks

Run `python blueprint/checks/check_special_function_identities.py` from the
repository root. It needs only Python's standard library and uses exact
`fractions.Fraction` arithmetic.

The current check exercises 365 finite identities and inequalities: 81 for
recentring and majorants, 124 for Bessel recurrences, sign bounds and zero
bracketing, 80 hypergeometric coefficient equations, 60 Euler--Maclaurin
polynomial identities, 3 continued zeta values, and 17 flat-function and
asymptotic coefficient recurrences.

The Bessel root construction uses interval-valued alternating series and
trisection, not floating-point sign decisions. The resulting bracket is
narrower than `2^-30`. Decimal endpoints in the console output are only a
readable summary of the exact rational endpoints.

These are regression checks, not formal proofs of the manuscript's theorems.
The proofs must establish the uniform estimates, all-order recurrences,
termination, and compatibility between constructions. A finite number of
successful checks does not establish those universal assertions.
