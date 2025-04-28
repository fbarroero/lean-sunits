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
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∉ S), (v.asIdeal.carrier)ᶜ) ∩ (nonZeroDivisors R)
  mul_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, mul_eq_zero, not_or, and_imp]
    intro a b ha ha0 hb hb0
    refine ⟨?_ , ha0, hb0⟩
    intro v hv
    specialize ha v hv
    specialize hb v hv
    refine Ideal.IsPrime.mul_not_mem ?_ ha hb
    exact v.isPrime
  one_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true, and_true]
    intro v hv
    refine (Ideal.ne_top_iff_one v.asIdeal).mp ?_
    exact Ideal.IsPrime.ne_top'
}

instance : IsLocalization (M S) <| S.integer K where
  map_units' := by
    simp only [M, Submodule.carrier_eq_coe, IsUnit, Subtype.forall, Submonoid.mem_mk,
      Subsemigroup.mem_mk, mem_iInter, mem_compl_iff, SetLike.mem_coe]
    intro r hr
    have h₀ : r ≠ 0 := by
      simp_all only [mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero, ne_eq,
        not_false_eq_true]
    let x : Kˣ := {
      val := algebraMap R K r
      inv := (algebraMap R K r)⁻¹
      val_inv := by simp [h₀]
      inv_val := by simp [h₀]
    }
    have : x ∈ S.unit K := by
      simp only [unit, x]
      intro v hv
      simp_all only [x]
      have := hr.1
      have hmem : r ∈ (v.asIdeal.carrier)ᶜ := by
        simp_all only [mem_inter_iff, SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero, ne_eq, not_false_eq_true,
          and_self, mem_iInter, mem_compl_iff, Submodule.carrier_eq_coe, x]
      simp at hmem
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_apply]
      have := v.intValuation_le_one r
      rw [le_iff_lt_or_eq] at this
      have : ¬ v.intValuationDef r < 1 := by
        rw [v.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]
        exact hmem
      simp_all
    use unitEquivUnitsInteger S K ⟨x, this⟩
    simp_all only [x]
    rfl
  surj' := sorry
  exists_of_eq := sorry


end

end Set
