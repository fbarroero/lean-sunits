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
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∉ S), (v.asIdeal.carrier)ᶜ)
  mul_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_iInter, mem_compl_iff, SetLike.mem_coe]
    intro a b ha hb v hv
    specialize ha v hv
    specialize hb v hv
    refine Ideal.IsPrime.mul_not_mem ?_ ha hb
    exact v.isPrime
  one_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_iInter, mem_compl_iff, SetLike.mem_coe]
    intro v hv
    refine (Ideal.ne_top_iff_one v.asIdeal).mp ?_
    exact Ideal.IsPrime.ne_top'
}

instance : IsLocalization (M S) <| S.integer K where
  map_units' := by
    simp only [M, Submodule.carrier_eq_coe, Subtype.forall, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_iInter, mem_compl_iff, SetLike.mem_coe]
    intro r hr

    --have (x :   (S.integer K)ˣ) :
    sorry
  surj' := sorry
  exists_of_eq := sorry


end

end Set
