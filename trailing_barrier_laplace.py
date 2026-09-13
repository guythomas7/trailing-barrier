#=====================#
# DISCLAIMER
# This  code is provided "as is" and "with all faults" for educational and research use only.  
#   The author makes no representations or warranties of any kind concerning its correctness or 
#   suitability for any particular purposes.  R.G.ThomasNOSPAM AT kent.ac.uk
#=====================#


"""
Exact Laplace-domain pricing for a put on geometric Brownian motion
reflected at a trailing barrier b times its own running maximum.

Model under the drift-neutralised measure Q_N:
    d log(N_t) = (r - q - sigma^2/2) dt + sigma dW_t.

The trailing-reflected asset starts at its running maximum:
    Y_0 = M_0 = S0,
and is reflected at b M_t.

The implementation uses the exact joint Laplace transform of:
    D_t = log(M_t / Y_t) in [0, -log(b)]
and the accumulated reflection R_t at D=0, for which
    log(Y_t/S0) = R_t - D_t.

The remaining numerical operation is one inverse Laplace transform in time.
Requires: mpmath
"""

from __future__ import annotations

import mpmath as mp


def _exp_integral(z: mp.mpc, lo: mp.mpf, hi: mp.mpf) -> mp.mpc:
    """Integral_lo^hi exp(z*x) dx, evaluated stably."""
    if abs(z) < mp.mpf("1e-25"):
        return hi - lo
    return mp.exp(z * lo) * mp.expm1(z * (hi - lo)) / z


def _kernel_quantities(
    s: mp.mpc,
    b: float,
    r: float,
    q: float,
    sigma: float,
):
    """
    Return a, gamma, rho, psi0, Lambda, and exponential coefficients
    for H_s(d) = h_minus exp(lambda_minus d) + h_plus exp(lambda_plus d).
    """
    a = -mp.log(b)
    nu = q - r + mp.mpf("0.5") * sigma**2
    gamma = nu / sigma**2
    rho = mp.sqrt(gamma**2 + 2 * s / sigma**2)

    psi0 = (
        mp.cosh(rho * a)
        - (gamma / rho) * mp.sinh(rho * a)
    )

    Lambda = (
        (rho**2 - gamma**2) * mp.sinh(rho * a)
        / (rho * mp.cosh(rho * a) - gamma * mp.sinh(rho * a))
    )

    lambda_minus = gamma - rho
    lambda_plus = gamma + rho

    h_minus = (
        (1 - gamma / rho) * mp.exp(rho * a)
        / (sigma**2 * psi0)
    )
    h_plus = (
        (1 + gamma / rho) * mp.exp(-rho * a)
        / (sigma**2 * psi0)
    )

    return (
        a,
        gamma,
        rho,
        psi0,
        Lambda,
        lambda_minus,
        lambda_plus,
        h_minus,
        h_plus,
    )


def put_payoff_laplace(
    s: complex,
    S0: float,
    K: float,
    b: float,
    r: float,
    q: float,
    sigma: float,
):
    """
    Laplace transform in maturity T of the *undiscounted* expected payoff:
        G(T) = E_QN[(K - Y_T)^+].

    Thus the transform of the discounted put value is Ghat(s+r).
    """
    if not (S0 > 0 and K > 0 and 0 < b < 1 and sigma > 0):
        raise ValueError("Require S0>0, K>0, 0<b<1, sigma>0.")

    s = mp.mpc(s)
    (
        a,
        gamma,
        rho,
        psi0,
        Lambda,
        lambda_minus,
        lambda_plus,
        h_minus,
        h_plus,
    ) = _kernel_quantities(s, b, r, q, sigma)

    k = mp.log(K / S0)
    d0 = max(mp.mpf("0"), -k)

    # If K <= b*S0, the put can never finish in the money.
    if d0 >= a:
        return mp.mpc("0")

    # Rare removable singularity Lambda = 1:
    # use the original finite d-integral in a small neighbourhood.
    if abs(Lambda - 1) < mp.mpf("1e-14"):
        def psi(d):
            return (
                mp.cosh(rho * (a - d))
                - (gamma / rho) * mp.sinh(rho * (a - d))
            )

        def H(d):
            return 2 / sigma**2 * mp.exp(gamma * d) * psi(d) / psi0

        def J(d):
            z = d + k
            first = K * (-mp.expm1(-Lambda * z)) / Lambda
            second = S0 * mp.exp(-d) * z
            return first - second

        return mp.quad(lambda d: H(d) * J(d), [d0, a])

    A0 = K / Lambda
    A1 = -S0 / (Lambda - 1)
    AL = (
        -K * mp.exp(-Lambda * k) / Lambda
        + S0 * mp.exp(-(Lambda - 1) * k) / (Lambda - 1)
    )

    def contribution(h, lam):
        return h * (
            A0 * _exp_integral(lam, d0, a)
            + A1 * _exp_integral(lam - 1, d0, a)
            + AL * _exp_integral(lam - Lambda, d0, a)
        )

    return (
        contribution(h_minus, lambda_minus)
        + contribution(h_plus, lambda_plus)
    )


def put_price(
    T: float,
    S0: float,
    K: float,
    b: float,
    r: float,
    q: float,
    sigma: float,
    method: str = "dehoog",
    dps: int = 35,
):
    """
    Discounted trailing-barrier put value at maturity T.

    method may be 'dehoog', 'talbot', or 'cohen'.
    Agreement between two or more methods is a useful numerical check.
    """
    if T <= 0:
        return max(K - S0, 0.0)

    with mp.workdps(dps):
        transform = lambda s: put_payoff_laplace(
            s + r, S0, K, b, r, q, sigma
        )
        return +mp.invertlaplace(transform, T, method=method)


def log_density_laplace(
    s: complex,
    z: float,
    b: float,
    r: float,
    q: float,
    sigma: float,
):
    """
    Laplace transform in t of the density of:
        Z_t = log(Y_t/S0).

    It does not depend on S0.  Support: z >= log(b).
    """
    s = mp.mpc(s)
    (
        a,
        gamma,
        rho,
        psi0,
        Lambda,
        lambda_minus,
        lambda_plus,
        h_minus,
        h_plus,
    ) = _kernel_quantities(s, b, r, q, sigma)

    z = mp.mpf(z)
    if z < -a:
        return mp.mpc("0")

    lo = max(mp.mpf("0"), -z)

    integral = (
        h_minus * _exp_integral(lambda_minus - Lambda, lo, a)
        + h_plus * _exp_integral(lambda_plus - Lambda, lo, a)
    )
    return mp.exp(-Lambda * z) * integral


def log_density(
    T: float,
    z: float,
    b: float,
    r: float,
    q: float,
    sigma: float,
    method: str = "dehoog",
    dps: int = 35,
):
    """Time-domain density of log(Y_T/S0), by inverse Laplace transform."""
    with mp.workdps(dps):
        transform = lambda s: log_density_laplace(
            s, z, b, r, q, sigma
        )
        return +mp.invertlaplace(transform, T, method=method)


def asset_density(
    T: float,
    y: float,
    S0: float,
    b: float,
    r: float,
    q: float,
    sigma: float,
    method: str = "dehoog",
    dps: int = 35,
):
    """Density of Y_T at y."""
    if y < b * S0:
        return mp.mpf("0")
    z = mp.log(y / S0)
    return log_density(T, z, b, r, q, sigma, method, dps) / y


if __name__ == "__main__":
    mp.mp.dps = 35

    example_1 = dict(
        T=25, S0=1, K=1.5, b=0.5,
        r=0.055, q=0.045, sigma=0.13,
    )
    example_2 = dict(
        T=10, S0=1, K=1.0, b=0.6,
        r=0.015, q=0.01, sigma=0.20,
    )

    for i, pars in enumerate((example_1, example_2), start=1):
        print(f"Example {i}")
        for method in ("talbot", "dehoog", "cohen"):
            value = put_price(**pars, method=method, dps=35)
            print(f"  {method:7s}: {mp.nstr(value, 16)}")
