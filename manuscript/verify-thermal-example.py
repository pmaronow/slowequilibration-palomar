#!/usr/bin/env python3
"""Exact certificate for xi(r)=r^4+b*r^12 in the standalone manuscript.

Run with Python 3; only the standard library is needed.  All computations
use integers and fractions.Fraction.  The irrational parameter t is enclosed
once, and every polynomial certificate covers its entire enclosing interval.
No floating-point arithmetic, sampling, or numerical root finder is used.
"""

from fractions import Fraction as F
from math import comb


T_LO = F(4539, 100000)
T_HI = F(4541, 100000)


def log6_bounds(n):
    """n positive-series terms and an upper bound on the remaining tail."""
    y = F(5, 7)
    lower = 2 * sum((y ** (2 * k + 1) / (2 * k + 1)
                     for k in range(n)), F(0))
    remainder = 2 * y ** (2 * n + 1) / ((2 * n + 1) * (1 - y * y))
    return lower, lower + remainder


def log_at_t(t):
    """Inverse of t=(45-24*log(6))/(72*log(6)-85)."""
    return (45 + 85 * t) / (24 + 72 * t)


def polynomial(t):
    p = [F(0) for _ in range(13)]
    p[0] = 24 + 72 * t
    p[2], p[3], p[4] = F(-432), F(720), F(-300)
    p[10], p[11], p[12] = -4752 * t, 7920 * t, -3300 * t
    return p


def derivative(p):
    return [j * p[j] for j in range(1, len(p))]


def evaluate(p, x):
    answer = F(0)
    for coefficient in reversed(p):
        answer = answer * x + coefficient
    return answer


def bernstein(p, a, b):
    """Coefficients in B_{k,n}(y), after r=a+(b-a)y, 0<=y<=1."""
    n = len(p) - 1
    power = [(b - a) ** j * sum(
        (p[i] * comb(i, j) * a ** (i - j) for i in range(j, n + 1)),
        F(0)) for j in range(n + 1)]
    coefficients = [sum((power[j] * F(comb(k, j), comb(n, j))
                         for j in range(k + 1)), F(0))
                    for k in range(n + 1)]
    # Endpoints provide independent checks of the basis conversion.
    assert coefficients[0] == evaluate(p, a)
    assert coefficients[-1] == evaluate(p, b)
    return coefficients


def main():
    # For y=5/7, log(6)=2*atanh(y), with a positive series.  The omitted
    # denominators are >=2*n+1, so the stated geometric tail bounds it.
    n = 13
    lo, hi = log6_bounds(n)
    assert F(85, 72) < lo
    assert log_at_t(T_HI) < lo < hi < log_at_t(T_LO)
    assert 72 * lo - 85 > 0
    # t(log) has derivative -1200/(72*log-85)^2.  The endpoint
    # comparisons above thus certify the stated open rational t interval.
    print(f"log(6): {n} positive-series terms suffice")
    print(f"{log_at_t(T_HI)} < log(6) < {log_at_t(T_LO)}")
    print(f"{T_LO} < t < {T_HI}")

    p = [polynomial(t) for t in (T_LO, T_HI)]
    dp = [derivative(q) for q in p]
    tasks = [
        ("P_t", p, F(0), F(357, 1000), 1, F(2, 25)),
        ("P_t", p, F(359, 1000), F(890, 1000), -1, F(1, 25)),
        ("P_t", p, F(892, 1000), F(1), 1, F(2, 25)),
        ("P_t'", dp, F(357, 1000), F(359, 1000), -1, F(86)),
        ("P_t'", dp, F(890, 1000), F(892, 1000), 1, F(73)),
    ]
    total_coefficients = 0
    for name, polynomials, a, b, sign, margin in tasks:
        coefficients = [bernstein(q, a, b) for q in polynomials]
        assert all(sign * c > margin for row in coefficients for c in row)
        coefficients = 2 * len(polynomials[0])
        total_coefficients += coefficients
        relation = ">" if sign == 1 else "<"
        bound = margin if sign == 1 else -margin
        print(f"{name} {relation} {bound} on [{a}, {b}]; "
              f"{coefficients} endpoint coefficients")
    print(f"Total: {total_coefficients} strict coefficient inequalities; "
          "no subdivisions")

    # mu(t) is strictly increasing: its derivative is
    # 2304/(24+72*t)^2.  This certificate proves even mu<2/3.
    mu_upper = (12 + 132 * T_HI) / (6 * (4 + 12 * T_HI))
    assert T_HI < F(1, 21)
    assert mu_upper < F(2, 3)
    print(f"mu_Q < {mu_upper} < 2/3")
    Q = F(9, 10)
    for degree in (4, 12):
        # d/dq [(1-q)^2*q^(degree-2)] has sign
        # (degree-2)-degree*q on 0<q<1.
        assert (degree - 2) - degree * Q < 0
    print("Residual summands decrease strictly for 9/10 <= q < 1")

    w_lo = 11 * T_LO * F(25, 27) ** 8
    w_hi = 11 * T_HI * F(25, 27) ** 8
    assert F(1, 5) < w_lo < w_hi < F(1, 3)
    assert F(1, 4) < w_lo < w_hi < F(3, 10)
    print("1/5 < 1/4 < w < 3/10 < 1/3")
    print("8*(1-3*w)*(1-5*w) < 0: inverse square root is nonconvex")
    print("All exact rational checks passed.")


if __name__ == "__main__":
    main()
