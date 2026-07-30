import RealRooted.Tactic.FiniteSymbolPF

/-!
# Finite-symbol PF-bidiagonal tactic frontends

Thin wrappers for the conditional finite-symbol route in
`RealRooted.Tactic.FiniteSymbolPF`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_fsp_finite_symbol_backend_named)
  "rr_fsp_finite_symbol_backend" " using "
    "stable" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_stable_of_residual_factor_named)
  "rr_fsp_stable_of_residual_factor" " using "
    "factor" ":=" term ","
    "residual_stable" ":=" term :
  tactic

syntax (name := rr_fsp_stable_of_residual_certificate_named)
  "rr_fsp_stable_of_residual_certificate" " using "
    "certificate" ":=" term :
  tactic

syntax (name := rr_fsp_preserver_of_residual_certificate_named)
  "rr_fsp_preserver_of_residual_certificate" " using "
    "certificate" ":=" term :
  tactic

syntax (name := rr_fsp_quadratic_preserver_named)
  "rr_fsp_quadratic_preserver" " using "
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_quadratic_preserver_on_degree_named)
  "rr_fsp_quadratic_preserver_on_degree" " using "
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_second_derivative_preserver_named)
  "rr_fsp_second_derivative_preserver" " using "
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_second_derivative_preserver_on_degree_named)
  "rr_fsp_second_derivative_preserver_on_degree" " using "
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_shifted_second_derivative_preserver_named)
  "rr_fsp_shifted_second_derivative_preserver" " using "
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term :
  tactic

syntax (name := rr_fsp_second_derivative_sequence_named)
  "rr_fsp_second_derivative_sequence" " using "
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

syntax (name := rr_fsp_shifted_second_derivative_sequence_named)
  "rr_fsp_shifted_second_derivative_sequence" " using "
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "degree_ge_two" ":=" term ","
    "cubic_degree" ":=" term ","
    "residual_pf" ":=" term ","
    "alpha_nonneg" ":=" term ","
    "beta_nonneg" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_fsp_finite_symbol_backend using
        stable := $hstab:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact FiniteSymbolPF.finite_symbol_pf_bidiagonal_backend
          $hstab $halpha $hbeta)
  | `(tactic|
      rr_fsp_stable_of_residual_factor using
        factor := $hfac:term,
        residual_stable := $hres:term) =>
      `(tactic|
        exact FiniteSymbolPF.finiteSymbol_stable_of_residual_factor
          $hfac $hres)
  | `(tactic|
      rr_fsp_stable_of_residual_certificate using
        certificate := $hcert:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.finiteSymbol_stable_of_residual_certificate
            $hcert)
  | `(tactic|
      rr_fsp_preserver_of_residual_certificate using
        certificate := $hcert:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.bidiagonalPFPreserver_of_finiteSymbol_residual_certificate
            $hcert)
  | `(tactic|
      rr_fsp_quadratic_preserver using
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.quadraticBidiagonalPFPreserver_of_residual_certificate
            _ _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_quadratic_preserver_on_degree using
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.quadraticBidiagonalPFPreserver_of_residual_certificate_on_degree
            _ _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_second_derivative_preserver using
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.secondDerivativeBidiagonalPFPreserver_of_residual_certificate
            _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_second_derivative_preserver_on_degree using
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.secondDerivativeBidiagonalPFPreserver_of_residual_certificate_on_degree
            _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_shifted_second_derivative_preserver using
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term) =>
      `(tactic|
        exact
          FiniteSymbolPF.shiftedSecondDerivativeBidiagonalPFPreserver_of_residual_certificate
            _ _ _ _ _ $hd $hdeg $hpf $halpha $hbeta)
  | `(tactic|
      rr_fsp_second_derivative_sequence using
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
            $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_second_derivative_sequence using
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from
            $N $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_shifted_second_derivative_sequence using
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.isPFPolynomial_of_shiftedSecondDerivativeBidiagonalForm_sequence
            $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_fsp_shifted_second_derivative_sequence using
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdegree:term,
        degree_ge_two := $hd:term,
        cubic_degree := $hdeg:term,
        residual_pf := $hpf:term,
        alpha_nonneg := $halpha:term,
        beta_nonneg := $hbeta:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (FiniteSymbolPF.isPFPolynomial_of_shiftedSecondDerivativeBidiagonalForm_sequence_from
            $N $hbase $hdegree $hd $hdeg $hpf $halpha $hbeta $hrec)
          $[, nonzero := $hne]?)

end Tactic
end RealRooted
