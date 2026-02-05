import Mathlib

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum nonZeroDivisors


variable
  {R : Type*} [CommRing R] [IsDedekindDomain R]
  (v : HeightOneSpectrum R)
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

lemma foo (x : K) (h : x ≠ 0) : v.valuation K x = 1 ↔
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x) = 0 := by
  sorry
