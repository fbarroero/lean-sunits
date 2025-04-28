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
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∈ S), (v.asIdeal.carrier)ᶜ)
  mul_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_iInter, mem_compl_iff, SetLike.mem_coe]
    intro a b ha hb v hv
    specialize ha v hv
    specialize hb v hv

    sorry
  one_mem' := sorry
}



instance : IsLocalization (R := R) (M S) <| S.integer K where
  map_units' := sorry
  surj' := sorry
  exists_of_eq := sorry


end

end Set
