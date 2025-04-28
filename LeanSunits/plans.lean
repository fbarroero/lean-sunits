import Mathlib

namespace Set

noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
-- {R_S : Type u} [CommRing R_S] [IsLocalization M ]
-- M = (union of primes in S)^c = (intersection of complements)

def M : Submonoid R := {
  carrier := ⊓ (v) (_ : v ∈ S), (v.asIdeal.carrier)ᶜ
  mul_mem' := sorry
  one_mem' := sorry
}

instance : IsLocalization M <| S.integer K :=


end

end Set
