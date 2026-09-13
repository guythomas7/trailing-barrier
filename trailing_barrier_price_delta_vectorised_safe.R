#=============================================================
# DISCLAIMER
# This  code is provided "as is" and "with all faults" for 
# educational and research use only. The author makes no 
# representations or warranties of any kind concerning its 
# correctness or suitability for any particular purposes.  
# R.G.ThomasNOSPAM AT kent.ac.uk
#=============================================================



# ============================================================
# Exact Laplace-domain pricing for a put on GBM reflected at
# a trailing barrier b times its own running maximum
# ============================================================
#
# Model under the drift-neutralised measure Q_N:
#
#   d log(N_t) = (r - q - sigma^2/2) dt + sigma dW_t.
#
# The trailing-reflected asset starts at its running maximum:
#
#   Y_0 = M_0 = S0,
#
# and is reflected at b M_t.
#
# The implementation uses the exact joint Laplace transform of
#
#   D_t = log(M_t / Y_t) in [0, -log(b)]
#
# and the accumulated reflection R_t at D = 0, for which
#
#   log(Y_t / S0) = R_t - D_t.
#
# The remaining numerical operation is one inverse Laplace
# transform in time.
#
# Dependency:
#   install.packages("pracma")
#
# The inverse transform uses pracma::invlap().
#
# IMPORTANT:
#   * S0 is assumed to equal the current running maximum M0.
#   * Continuous monitoring is assumed.
#   * This is a double-precision R implementation. For unusually
#     extreme parameters, compare several ILT shift values and/or
#     cross-check against the arbitrary-precision Python version.
# ============================================================


# --------------------------
# Package check
# --------------------------

if (!requireNamespace("pracma", quietly = TRUE)) {
  stop(
    "Package 'pracma' is required. Install it with:\n",
    "install.packages('pracma')"
  )
}


# --------------------------
# Small numerical helpers
# --------------------------

.tb_complex_expm1 <- function(z) {
  # Stable exp(z) - 1 for a scalar real or complex z.
  if (Mod(z) < 1e-6) {
    return(
      z +
        z^2 / 2 +
        z^3 / 6 +
        z^4 / 24 +
        z^5 / 120 +
        z^6 / 720
    )
  }

  exp(z) - 1
}


.tb_exp_integral <- function(z, lower, upper) {
  # Integral_lower^upper exp(z*x) dx.
  if (Mod(z) < 1e-10) {
    return(as.complex(upper - lower))
  }

  exp(z * lower) *
    .tb_complex_expm1(z * (upper - lower)) / z
}


.tb_exp_integral_moment1 <- function(z, lower, upper) {
  # Integral_lower^upper x exp(z*x) dx.

  if (Mod(z) < 1e-5) {
    # Power-series evaluation near z = 0.
    ans <- 0 + 0i

    for (n in 0:8) {
      ans <- ans +
        z^n / factorial(n) *
        (upper^(n + 2) - lower^(n + 2)) / (n + 2)
    }

    return(ans)
  }

  (
    exp(z * upper) * (z * upper - 1) -
      exp(z * lower) * (z * lower - 1)
  ) / z^2
}


.tb_integral_exp_J <- function(lambda, a, k, lower, upper) {
  # Integral exp(lambda*d) J(a, d+k) dd,
  #
  # where
  #
  #   J(a, L) = (1 - exp(-a L))/a,
  #
  # with limiting value J(0, L) = L.

  if (Mod(a) < 1e-8) {
    return(
      .tb_exp_integral_moment1(lambda, lower, upper) +
        k * .tb_exp_integral(lambda, lower, upper)
    )
  }

  (
    .tb_exp_integral(lambda, lower, upper) -
      exp(-a * k) *
        .tb_exp_integral(lambda - a, lower, upper)
  ) / a
}


# --------------------------
# Laplace-kernel quantities
# --------------------------

.tb_kernel_quantities <- function(s, b, r, q, sigma) {
  A <- -log(b)

  nu <- q - r + 0.5 * sigma^2
  gamma <- nu / sigma^2

  rho <- sqrt(gamma^2 + 2 * s / sigma^2)

  # Principal square root already has non-negative real part in
  # standard R complex arithmetic, but enforce the required branch.
  if (Re(rho) < 0) {
    rho <- -rho
  }

  x <- rho * A

  # Scaled representation of
  #
  #   psi0 = cosh(x) - (gamma/rho) sinh(x),
  #
  # avoiding unnecessary overflow when Re(x) is large:
  #
  #   psi0_scaled = exp(-x) psi0.
  e_minus_2x <- exp(-2 * x)

  psi0_scaled <- 0.5 * (
    (1 - gamma / rho) +
      (1 + gamma / rho) * e_minus_2x
  )

  numerator_scaled <- 0.5 * (
    rho^2 - gamma^2
  ) * (1 - e_minus_2x)

  denominator_scaled <- 0.5 * (
    (rho - gamma) +
      (rho + gamma) * e_minus_2x
  )

  Lambda <- numerator_scaled / denominator_scaled

  lambda_minus <- gamma - rho
  lambda_plus <- gamma + rho

  h_minus <- (
    1 - gamma / rho
  ) / (sigma^2 * psi0_scaled)

  h_plus <- (
    1 + gamma / rho
  ) * e_minus_2x / (sigma^2 * psi0_scaled)

  list(
    A = A,
    gamma = gamma,
    rho = rho,
    Lambda = Lambda,
    lambda_minus = lambda_minus,
    lambda_plus = lambda_plus,
    h_minus = h_minus,
    h_plus = h_plus
  )
}


# ============================================================
# Put payoff transform and price
# ============================================================

trailing_put_payoff_laplace_scalar <- function(
    s,
    S0,
    K,
    b,
    r,
    q,
    sigma
) {
  # Laplace transform in maturity T of the undiscounted expected
  # payoff:
  #
  #   G(T) = E_QN[(K - Y_T)^+].
  #
  # The transform of the discounted put value is therefore
  # Ghat(s + r).

  if (
    !is.finite(S0) || !is.finite(K) ||
      !is.finite(b) || !is.finite(r) ||
      !is.finite(q) || !is.finite(sigma)
  ) {
    stop("All model parameters must be finite.")
  }

  if (S0 <= 0 || K <= 0 || b <= 0 || b >= 1 || sigma <= 0) {
    stop("Require S0 > 0, K > 0, 0 < b < 1, and sigma > 0.")
  }

  s <- as.complex(s)

  ker <- .tb_kernel_quantities(
    s = s,
    b = b,
    r = r,
    q = q,
    sigma = sigma
  )

  A <- ker$A
  Lambda <- ker$Lambda

  k <- log(K / S0)
  d0 <- max(0, -k)

  # Since Y_T >= b*S0, the put can never finish in the money
  # when K <= b*S0.
  if (d0 >= A) {
    return(0 + 0i)
  }

  contribution <- function(h, lambda) {
    h * (
      K * .tb_integral_exp_J(
        lambda = lambda,
        a = Lambda,
        k = k,
        lower = d0,
        upper = A
      ) -
        S0 * .tb_integral_exp_J(
          lambda = lambda - 1,
          a = Lambda - 1,
          k = k,
          lower = d0,
          upper = A
        )
    )
  }

  contribution(
    h = ker$h_minus,
    lambda = ker$lambda_minus
  ) +
    contribution(
      h = ker$h_plus,
      lambda = ker$lambda_plus
    )
}


trailing_put_payoff_laplace <- function(
    s,
    S0,
    K,
    b,
    r,
    q,
    sigma
) {
  # Vectorised wrapper required by pracma::invlap().

  vapply(
    s,
    FUN = function(si) {
      trailing_put_payoff_laplace_scalar(
        s = si,
        S0 = S0,
        K = K,
        b = b,
        r = r,
        q = q,
        sigma = sigma
      )
    },
    FUN.VALUE = complex(1)
  )
}


trailing_put_price <- function(
    tau,
    S0,
    K,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19,
    warn = TRUE
) {
  # Discounted put value at maturity tau.
  #
  # The inverse-Laplace settings ilt_shift = 10, ilt_ns = 20,
  # ilt_nd = 19 have worked accurately over the parameter ranges
  # tested. For an important result, compare ilt_shift values
  # 8, 10 and 12 using trailing_put_price_check() below.

  if (length(tau) != 1L || !is.finite(tau)) {
    stop("tau must be one finite scalar.")
  }

  if (tau <= 0) {
    return(max(K - S0, 0))
  }

  if (K <= b * S0) {
    return(0)
  }

  transform <- function(s) {
    trailing_put_payoff_laplace(
      s = s + r,
      S0 = S0,
      K = K,
      b = b,
      r = r,
      q = q,
      sigma = sigma
    )
  }

  inversion <- pracma::invlap(
    Fs = transform,
    t1 = tau,
    t2 = tau,
    nnt = 1,
    a = ilt_shift,
    ns = ilt_ns,
    nd = ilt_nd
  )

  value <- as.numeric(inversion$y[1])

  # Remove harmless negative roundoff.
  if (value < 0 && value > -1e-10) {
    value <- 0
  }

  if (warn) {
    upper_bound <- exp(-r * tau) * max(K - b * S0, 0)

    if (!is.finite(value)) {
      warning("Inverse Laplace transform returned a non-finite value.")
    } else {
      if (value < -1e-8) {
        warning(
          "Inverse Laplace transform returned a materially negative put value: ",
          signif(value, 8)
        )
      }

      if (
        is.finite(upper_bound) &&
          value > upper_bound + 1e-7 * max(1, upper_bound)
      ) {
        warning(
          "Computed put value exceeds the elementary payoff bound."
        )
      }
    }
  }

  value
}


trailing_put_price_check <- function(
    tau,
    S0,
    K,
    b,
    r,
    q,
    sigma,
    shifts = c(8, 10, 12),
    ilt_ns = 20,
    ilt_nd = 19
) {
  # Numerical-stability check across several inversion shifts.

  values <- vapply(
    shifts,
    FUN = function(shift) {
      trailing_put_price(
        tau = tau,
        S0 = S0,
        K = K,
        b = b,
        r = r,
        q = q,
        sigma = sigma,
        ilt_shift = shift,
        ilt_ns = ilt_ns,
        ilt_nd = ilt_nd,
        warn = FALSE
      )
    },
    FUN.VALUE = numeric(1)
  )

  data.frame(
    ilt_shift = shifts,
    put_value = values,
    difference_from_last = values - tail(values, 1),
    row.names = NULL
  )
}


# ============================================================
# Marginal density of log(Y_T/S0) and of Y_T
# ============================================================

trailing_log_density_laplace_scalar <- function(
    s,
    z,
    b,
    r,
    q,
    sigma
) {
  # Laplace transform in t of the density of
  #
  #   Z_t = log(Y_t / S0).
  #
  # The result does not depend on S0.
  # Support: z >= log(b).

  if (b <= 0 || b >= 1 || sigma <= 0) {
    stop("Require 0 < b < 1 and sigma > 0.")
  }

  s <- as.complex(s)

  ker <- .tb_kernel_quantities(
    s = s,
    b = b,
    r = r,
    q = q,
    sigma = sigma
  )

  A <- ker$A

  if (z < -A) {
    return(0 + 0i)
  }

  lower <- max(0, -z)

  integral <- ker$h_minus *
    .tb_exp_integral(
      ker$lambda_minus - ker$Lambda,
      lower,
      A
    ) +
    ker$h_plus *
      .tb_exp_integral(
        ker$lambda_plus - ker$Lambda,
        lower,
        A
      )

  exp(-ker$Lambda * z) * integral
}


trailing_log_density_laplace <- function(
    s,
    z,
    b,
    r,
    q,
    sigma
) {
  vapply(
    s,
    FUN = function(si) {
      trailing_log_density_laplace_scalar(
        s = si,
        z = z,
        b = b,
        r = r,
        q = q,
        sigma = sigma
      )
    },
    FUN.VALUE = complex(1)
  )
}


trailing_log_density <- function(
    tau,
    z,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19
) {
  if (tau <= 0) {
    stop("The density function requires tau > 0.")
  }

  if (z < log(b)) {
    return(0)
  }

  transform <- function(s) {
    trailing_log_density_laplace(
      s = s,
      z = z,
      b = b,
      r = r,
      q = q,
      sigma = sigma
    )
  }

  inversion <- pracma::invlap(
    Fs = transform,
    t1 = tau,
    t2 = tau,
    nnt = 1,
    a = ilt_shift,
    ns = ilt_ns,
    nd = ilt_nd
  )

  value <- as.numeric(inversion$y[1])

  if (value < 0 && value > -1e-9) {
    value <- 0
  }

  value
}


trailing_asset_density <- function(
    tau,
    y,
    S0,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19
) {
  if (y < b * S0) {
    return(0)
  }

  z <- log(y / S0)

  trailing_log_density(
    tau = tau,
    z = z,
    b = b,
    r = r,
    q = q,
    sigma = sigma,
    ilt_shift = ilt_shift,
    ilt_ns = ilt_ns,
    ilt_nd = ilt_nd
  ) / y
}


# ============================================================
# Grid helper for comparison with Monte Carlo
# ============================================================

trailing_put_price_grid <- function(
    parameter_grid,
    mc_column = NULL,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19,
    progress = TRUE
) {
  # parameter_grid must contain:
  #   tau, S0, K, b, r, q, sigma
  #
  # If mc_column is supplied, it should name a column containing
  # Monte Carlo put values. Difference and ratio columns are added.

  required <- c("tau", "S0", "K", "b", "r", "q", "sigma")
  missing <- setdiff(required, names(parameter_grid))

  if (length(missing) > 0) {
    stop(
      "parameter_grid is missing required columns: ",
      paste(missing, collapse = ", ")
    )
  }

  out <- parameter_grid
  n <- nrow(out)

  out$Laplace_put_price <- NA_real_

  for (i in seq_len(n)) {
    if (progress) {
      message("Laplace inversion: case ", i, " of ", n)
    }

    out$Laplace_put_price[i] <- trailing_put_price(
      tau = out$tau[i],
      S0 = out$S0[i],
      K = out$K[i],
      b = out$b[i],
      r = out$r[i],
      q = out$q[i],
      sigma = out$sigma[i],
      ilt_shift = ilt_shift,
      ilt_ns = ilt_ns,
      ilt_nd = ilt_nd
    )
  }

  if (!is.null(mc_column)) {
    if (!mc_column %in% names(out)) {
      stop("mc_column is not a column in parameter_grid.")
    }

    mc <- out[[mc_column]]

    out$Laplace_less_MC <-
      out$Laplace_put_price - mc

    out$Laplace_to_MC_ratio <- ifelse(
      is.finite(mc) & mc != 0,
      out$Laplace_put_price / mc,
      NA_real_
    )
  }

  out
}


# ============================================================
# Examples
# ============================================================
#
# Example 1:
#
# trailing_put_price_check(
#   tau = 25,
#   S0 = 1,
#   K = 1.5,
#   b = 0.5,
#   r = 0.055,
#   q = 0.045,
#   sigma = 0.13
# )
#
# Expected value approximately:
#
#   0.0891345086
#
#
# Example 2:
#
# trailing_put_price_check(
#   tau = 10,
#   S0 = 1,
#   K = 1.0,
#   b = 0.6,
#   r = 0.015,
#   q = 0.010,
#   sigma = 0.20
# )
#
# Expected value approximately:
#
#   0.0466427423
#
#
# Example grid:
#
# grid <- expand.grid(
#   tau = c(10, 20, 25),
#   S0 = 1,
#   K = c(1.0, 1.5),
#   b = c(0.4, 0.5, 0.6),
#   r = 0.055,
#   q = 0.045,
#   sigma = c(0.13, 0.20),
#   KEEP.OUT.ATTRS = FALSE
# )
#
# values <- trailing_put_price_grid(grid)
#
# write.csv(
#   values,
#   "trailing_barrier_Laplace_values.csv",
#   row.names = FALSE
# )
#


# ============================================================
# General current state and exact put delta
# ============================================================
#
# At an intermediate time, supply:
#
#   y = current trailing-barrier asset price,
#   m = current running maximum,
#
# with b*m <= y <= m.
#
# Put:
#
#   x = log(m/y),  A = -log(b).
#
# The future price can be represented as
#
#   Y_{t+u} = m * exp(R_u - D_u),
#
# where D starts at x and is reflected on [0,A], and R is its
# accumulated reflection at D=0.
#
# The exact hedge delta is
#
#   Delta = partial P / partial y |_m
#         = -(1/y) partial P / partial x.
#
# The functions below analytically differentiate the general-state
# Laplace transform before performing the one-dimensional inverse
# Laplace transform in remaining time.
# ============================================================


.tb_integral_g0 <- function(lambda, m, K, lower, upper) {
  # Integral exp(lambda*d) * (K - m*exp(-d)) dd.

  if (upper <= lower) {
    return(0 + 0i)
  }

  K * .tb_exp_integral(lambda, lower, upper) -
    m * .tb_exp_integral(lambda - 1, lower, upper)
}


.tb_integral_g1 <- function(
    lambda,
    Lambda,
    k,
    m,
    K,
    lower,
    upper
) {
  # Integral exp(lambda*d) * g1(d) dd, where
  #
  # g1(d) =
  #   K J(Lambda, d+k)
  #   - m exp(-d) J(Lambda-1, d+k),
  #
  # J(a,L) = (1-exp(-aL))/a, with J(0,L)=L.

  if (upper <= lower) {
    return(0 + 0i)
  }

  K * .tb_integral_exp_J(
    lambda = lambda,
    a = Lambda,
    k = k,
    lower = lower,
    upper = upper
  ) -
    m * .tb_integral_exp_J(
      lambda = lambda - 1,
      a = Lambda - 1,
      k = k,
      lower = lower,
      upper = upper
    )
}


.tb_validate_state <- function(y, m, K, b, sigma) {
  if (
    length(y) != 1L || length(m) != 1L || length(K) != 1L ||
      length(b) != 1L || length(sigma) != 1L ||
      !all(is.finite(c(y, m, K, b, sigma)))
  ) {
    stop("y, m, K, b and sigma must each be one finite scalar.")
  }

  if (y <= 0 || m <= 0 || K <= 0 || b <= 0 || b >= 1 || sigma <= 0) {
    stop("Require y>0, m>0, K>0, 0<b<1 and sigma>0.")
  }

  tolerance <- 1e-10 * max(1, m)

  if (y > m + tolerance) {
    stop("The current price y cannot exceed the current running maximum m.")
  }

  if (y < b * m - tolerance) {
    stop("The current price y cannot lie below the trailing barrier b*m.")
  }

  # Remove harmless floating-point excursions at the state boundaries.
  min(max(y, b * m), m)
}


trailing_put_state_payoff_laplace_scalar <- function(
    s,
    y,
    m,
    K,
    b,
    r,
    q,
    sigma,
    derivative_x = FALSE
) {
  # Laplace transform in remaining maturity tau of
  #
  #   E_x[(K - m exp(R_tau-D_tau))^+],
  #
  # where x=log(m/y).
  #
  # If derivative_x=TRUE, return its analytical partial derivative
  # with respect to x, holding m and K fixed.

  y <- .tb_validate_state(y, m, K, b, sigma)
  s <- as.complex(s)

  ker <- .tb_kernel_quantities(
    s = s,
    b = b,
    r = r,
    q = q,
    sigma = sigma
  )

  A <- ker$A
  gamma <- ker$gamma
  rho <- ker$rho
  Lambda <- ker$Lambda

  x <- log(m / y)

  # Clamp tiny floating-point deviations.
  x <- min(max(x, 0), A)

  # Since the future running maximum cannot fall below m,
  # Y_T >= b*m on every future path.
  if (K <= b * m) {
    return(0 + 0i)
  }

  # At the lower trailing barrier the exact Neumann condition gives
  # partial P / partial x = 0, hence delta = 0.
  if (derivative_x && abs(x - A) <= 1e-12 * max(1, A)) {
    return(0 + 0i)
  }

  k <- log(K / m)
  d0 <- max(0, -k)

  if (d0 >= A) {
    return(0 + 0i)
  }

  lambda_minus <- ker$lambda_minus
  lambda_plus <- ker$lambda_plus

  interval_integrals <- function(lower, upper) {
    if (upper <= lower) {
      return(list(
        I0_minus = 0 + 0i,
        I0_plus = 0 + 0i,
        I1_minus = 0 + 0i,
        I1_plus = 0 + 0i
      ))
    }

    list(
      I0_minus = .tb_integral_g0(
        lambda_minus, m, K, lower, upper
      ),
      I0_plus = .tb_integral_g0(
        lambda_plus, m, K, lower, upper
      ),
      I1_minus = .tb_integral_g1(
        lambda_minus, Lambda, k, m, K, lower, upper
      ),
      I1_plus = .tb_integral_g1(
        lambda_plus, Lambda, k, m, K, lower, upper
      )
    )
  }

  answer <- 0 + 0i
  ccoef <- sigma^2 / 2

  # ----------------------------------------------------------
  # Region d < x:
  # u=d, v=x in the general Green kernel.
  # ----------------------------------------------------------

  lower_left <- d0
  upper_left <- min(x, A)

  if (upper_left > lower_left) {
    ints <- interval_integrals(lower_left, upper_left)

    # Expansions:
    #
    # exp(gamma*d) A1(d)
    #   = a1_minus exp(lambda_minus*d)
    #   + a1_plus exp(lambda_plus*d),
    #
    # exp(gamma*d) B(d)
    #   = B_minus exp(lambda_minus*d)
    #   + B_plus exp(lambda_plus*d),
    #
    # where B(d)=A0(d)-Lambda*A1(d).

    a1_minus <- -1 / (2 * rho)
    a1_plus <- 1 / (2 * rho)

    B_minus <- 0.5 * (
      1 - (gamma - Lambda) / rho
    )
    B_plus <- 0.5 * (
      1 + (gamma - Lambda) / rho
    )

    # Stable ratios to psi_s(0).
    denominator <- (
      1 - gamma / rho
    ) + (
      1 + gamma / rho
    ) * exp(-2 * rho * A)

    if (!derivative_x) {
      psi_ratio <- exp(-rho * x) * (
        (
          1 - gamma / rho
        ) + (
          1 + gamma / rho
        ) * exp(-2 * rho * (A - x))
      ) / denominator

      common_left <- exp(-gamma * x) *
        psi_ratio / ccoef
    } else {
      # [psi_s'(x) - gamma psi_s(x)] / psi_s(0)
      derivative_ratio <- -(
        rho^2 - gamma^2
      ) / rho *
        exp(-rho * x) *
        (
          1 - exp(-2 * rho * (A - x))
        ) / denominator

      common_left <- exp(-gamma * x) *
        derivative_ratio / ccoef
    }

    answer <- answer + common_left * (
      a1_minus * ints$I0_minus +
        a1_plus * ints$I0_plus +
        B_minus * ints$I1_minus +
        B_plus * ints$I1_plus
    )
  }

  # ----------------------------------------------------------
  # Region d >= x:
  # u=x, v=d in the general Green kernel.
  # ----------------------------------------------------------

  lower_right <- max(d0, x)
  upper_right <- A

  if (upper_right > lower_right) {
    ints <- interval_integrals(lower_right, upper_right)

    sinh_x <- sinh(rho * x)
    cosh_x <- cosh(rho * x)

    A1_x <- sinh_x / rho
    A0_x <- cosh_x + (gamma / rho) * sinh_x
    B_x <- A0_x - Lambda * A1_x

    if (!derivative_x) {
      atom_coefficient <- A1_x
      continuous_coefficient <- B_x
    } else {
      A1_prime_x <- cosh_x
      A0_prime_x <- rho * sinh_x + gamma * cosh_x
      B_prime_x <- A0_prime_x - Lambda * A1_prime_x

      atom_coefficient <- A1_prime_x - gamma * A1_x
      continuous_coefficient <- B_prime_x - gamma * B_x
    }

    atom_integral <- ker$h_minus * ints$I0_minus +
      ker$h_plus * ints$I0_plus

    continuous_integral <- ker$h_minus * ints$I1_minus +
      ker$h_plus * ints$I1_plus

    answer <- answer + exp(-gamma * x) * (
      atom_coefficient * atom_integral +
        continuous_coefficient * continuous_integral
    )
  }

  answer
}


trailing_put_state_payoff_laplace <- function(
    s,
    y,
    m,
    K,
    b,
    r,
    q,
    sigma,
    derivative_x = FALSE
) {
  # Vectorised wrapper required by pracma::invlap().

  vapply(
    s,
    FUN = function(si) {
      trailing_put_state_payoff_laplace_scalar(
        s = si,
        y = y,
        m = m,
        K = K,
        b = b,
        r = r,
        q = q,
        sigma = sigma,
        derivative_x = derivative_x
      )
    },
    FUN.VALUE = complex(1)
  )
}


.tb_inverse_laplace_scalar <- function(
    transform,
    tau,
    ilt_shift,
    ilt_ns,
    ilt_nd
) {
  inversion <- pracma::invlap(
    Fs = transform,
    t1 = tau,
    t2 = tau,
    nnt = 1,
    a = ilt_shift,
    ns = ilt_ns,
    nd = ilt_nd
  )

  as.numeric(inversion$y[1])
}


trailing_put_price_state <- function(
    tau,
    y,
    m,
    K,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19,
    warn = TRUE
) {
  # Exact discounted continuation value at a general current state.

  y <- .tb_validate_state(y, m, K, b, sigma)

  if (length(tau) != 1L || !is.finite(tau)) {
    stop("tau must be one finite scalar.")
  }

  if (tau <= 0) {
    return(max(K - y, 0))
  }

  if (K <= b * m) {
    return(0)
  }

  transform <- function(s) {
    trailing_put_state_payoff_laplace(
      s = s + r,
      y = y,
      m = m,
      K = K,
      b = b,
      r = r,
      q = q,
      sigma = sigma,
      derivative_x = FALSE
    )
  }

  value <- .tb_inverse_laplace_scalar(
    transform = transform,
    tau = tau,
    ilt_shift = ilt_shift,
    ilt_ns = ilt_ns,
    ilt_nd = ilt_nd
  )

  if (value < 0 && value > -1e-10) {
    value <- 0
  }

  if (warn) {
    upper_bound <- exp(-r * tau) * max(K - b * m, 0)

    if (!is.finite(value)) {
      warning("Inverse Laplace transform returned a non-finite value.")
    } else {
      if (value < -1e-8) {
        warning(
          "Inverse Laplace transform returned a materially negative value: ",
          signif(value, 8)
        )
      }

      if (
        value > upper_bound + 1e-7 * max(1, upper_bound)
      ) {
        warning(
          "Computed put value exceeds the elementary payoff bound."
        )
      }
    }
  }

  value
}


trailing_put_delta_state <- function(
    tau,
    y,
    m,
    K,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19,
    boundary_tolerance = 1e-10,
    warn = TRUE,
    fallback_ilt_shifts = c(8, 12),
    failure_value = NA_real_,
    delta_bounds = c(-1, 1),
    delta_bound_tolerance = 1e-6
) {
  # Exact delta:
  #
  #   partial P / partial y, holding the current running maximum m fixed.
  #
  # At y=m this is understood as the derivative from inside the
  # admissible state space. The lookback boundary condition makes it
  # equal to the hedge ratio when a new maximum is being established.
  #
  # Numerical robustness:
  #   * catches state-validation and inverse-Laplace errors;
  #   * rejects NA, NaN and Inf;
  #   * retries alternative inverse-Laplace shifts;
  #   * rejects materially out-of-range deltas;
  #   * returns failure_value instead of stopping the calling program.
  #
  # Attributes returned on a scalar result:
  #   delta_failed   TRUE/FALSE
  #   failure_reason text if all attempts fail
  #   ilt_shift_used successful inversion shift, where applicable

  .report_failure <- function(reason) {
    if (isTRUE(warn)) {
      try(
        warning(
          "trailing_put_delta_state(): ",
          reason,
          "; returning failure_value = ",
          format(failure_value, digits = 16),
          call. = FALSE
        ),
        silent = TRUE
      )
    }

    out <- as.numeric(failure_value)
    attr(out, "delta_failed") <- TRUE
    attr(out, "failure_reason") <- reason
    out
  }

  validated_y <- tryCatch(
    .tb_validate_state(y, m, K, b, sigma),
    error = function(e) e
  )

  if (inherits(validated_y, "error")) {
    return(.report_failure(conditionMessage(validated_y)))
  }

  y <- validated_y

  if (length(tau) != 1L || !is.finite(tau)) {
    return(.report_failure("tau must be one finite scalar"))
  }

  if (tau <= 0) {
    out <- if (y < K) -1 else if (y > K) 0 else -0.5
    attr(out, "delta_failed") <- FALSE
    attr(out, "calculation_type") <- "terminal"
    return(out)
  }

  if (K <= b * m) {
    out <- 0
    attr(out, "delta_failed") <- FALSE
    attr(out, "calculation_type") <- "worthless_put"
    return(out)
  }

  # Exact Neumann condition at the trailing barrier.
  if (abs(y - b * m) <= boundary_tolerance * max(1, m)) {
    out <- 0
    attr(out, "delta_failed") <- FALSE
    attr(out, "calculation_type") <- "barrier_boundary"
    return(out)
  }

  if (!is.null(delta_bounds)) {
    if (
      length(delta_bounds) != 2L ||
        any(!is.finite(delta_bounds)) ||
        delta_bounds[1] >= delta_bounds[2]
    ) {
      return(.report_failure(
        "delta_bounds must be NULL or two increasing finite numbers"
      ))
    }
  }

  transform <- function(s) {
    -trailing_put_state_payoff_laplace(
      s = s + r,
      y = y,
      m = m,
      K = K,
      b = b,
      r = r,
      q = q,
      sigma = sigma,
      derivative_x = TRUE
    ) / y
  }

  shifts_to_try <- unique(c(ilt_shift, fallback_ilt_shifts))
  shifts_to_try <- shifts_to_try[
    is.finite(shifts_to_try) & shifts_to_try > 0
  ]

  if (length(shifts_to_try) == 0L) {
    return(.report_failure("no valid inverse-Laplace shift was supplied"))
  }

  last_reason <- "no inverse-Laplace attempt was made"

  for (shift_now in shifts_to_try) {
    value <- tryCatch(
      .tb_inverse_laplace_scalar(
        transform = transform,
        tau = tau,
        ilt_shift = shift_now,
        ilt_ns = ilt_ns,
        ilt_nd = ilt_nd
      ),
      error = function(e) {
        last_reason <<- paste0(
          "inverse Laplace transform failed at ilt_shift = ",
          shift_now,
          ": ",
          conditionMessage(e)
        )
        NA_real_
      }
    )

    if (length(value) != 1L || !is.finite(value)) {
      last_reason <- paste0(
        "inverse Laplace transform returned a non-finite value at ",
        "ilt_shift = ",
        shift_now
      )
      next
    }

    value <- as.numeric(value)

    if (abs(value) < 1e-12) {
      value <- 0
    }

    if (!is.null(delta_bounds)) {
      lower <- delta_bounds[1]
      upper <- delta_bounds[2]

      if (
        value < lower - delta_bound_tolerance ||
          value > upper + delta_bound_tolerance
      ) {
        last_reason <- paste0(
          "inverse Laplace transform returned out-of-range delta ",
          format(value, digits = 16),
          " at ilt_shift = ",
          shift_now
        )
        next
      }

      # Clip only very small numerical excursions.
      value <- min(max(value, lower), upper)
    }

    if (shift_now != ilt_shift && isTRUE(warn)) {
      try(
        warning(
          "trailing_put_delta_state(): primary inversion at ilt_shift = ",
          ilt_shift,
          " failed or was rejected; fallback ilt_shift = ",
          shift_now,
          " succeeded.",
          call. = FALSE
        ),
        silent = TRUE
      )
    }

    attr(value, "delta_failed") <- FALSE
    attr(value, "ilt_shift_used") <- shift_now
    attr(value, "calculation_type") <- if (
      shift_now == ilt_shift
    ) {
      "primary_inversion"
    } else {
      "fallback_inversion"
    }

    return(value)
  }

  .report_failure(
    paste0(
      "all inverse-Laplace attempts failed or were rejected; ",
      last_reason
    )
  )
}


# Backwards-compatible shorter name used in some earlier scripts.
trailing_put_delta <- trailing_put_delta_state


trailing_put_price_delta_state <- function(
    tau,
    y,
    m,
    K,
    b,
    r,
    q,
    sigma,
    ilt_shift = 10,
    ilt_ns = 20,
    ilt_nd = 19
) {
  data.frame(
    tau = tau,
    y = y,
    m = m,
    drawdown_x = log(m / y),
    strike_ratio = K / m,
    price = trailing_put_price_state(
      tau = tau,
      y = y,
      m = m,
      K = K,
      b = b,
      r = r,
      q = q,
      sigma = sigma,
      ilt_shift = ilt_shift,
      ilt_ns = ilt_ns,
      ilt_nd = ilt_nd
    ),
    delta = trailing_put_delta(
      tau = tau,
      y = y,
      m = m,
      K = K,
      b = b,
      r = r,
      q = q,
      sigma = sigma,
      ilt_shift = ilt_shift,
      ilt_ns = ilt_ns,
      ilt_nd = ilt_nd
    )
  )
}

