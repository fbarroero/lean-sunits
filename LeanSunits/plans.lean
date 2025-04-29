import Mathlib

namespace Set

noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

--- M is the multiplicative submonoid consisting of all r ∈ R such that ν(r) ≥ 0 for all ν ∉ S. Note that we allow infinite sets S, for which M would contain 0 unless we intersect with (nonZeroDivisors R).

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

--- We prove that the S.integers are indeed a localization. Should probably not be here but in Sinteger.lean?

#count_heartbeats in
instance : IsLocalization (M S) <| S.integer K where
  map_units' := by sorry /- ## what is below should be commented out when working on thing below because it takes a bit to compile
    simp only [M, Submodule.carrier_eq_coe,  Subtype.forall, Submonoid.mem_mk,
      Subsemigroup.mem_mk]
    intro r hr
    have h₀ : r ≠ 0 := nonZeroDivisors.ne_zero hr.2
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
  -/
  surj' := by
    intro r
    simp only [Prod.exists, Subtype.exists, exists_prop]
    have : ∀ v ∉ S, v.valuation K (↑r : K) ≥ 0 := by sorry
    /- idea:
      (1) every r : ↥(S.integer K) is in the fraction field K of R.
      (2) we know that v(r) ≥ 0 for all ν ∉ S.
      (3) we know that v(r) < 0 at most for a finite subset T of S.
      (4) consider the ideal I = ∏ v \in T in R, p_v.
      (5) THIS DOES BREAK FOR A GENERAL DEDEKIND DOMAIN. (The Picard group of an elliptic curve is infinite.)
      The class group of R is finite (or better: torsion).
      (6) There exists an integer n≥1 such that I^n is principal, i.e., (α_T)=I^n. This α_T : R has to satisfy v(α)≥n≥1 if v ∈ T and v(α)=0 elsewise.
      (7) There exists an integer m≥1 such that β=(α_T^m)*r satisfies v(β)≥0.
      (8) This should imply β : R.
      (9) Use a_1 = (α_T^m) and a = β in goal.
      (10) Win ;-).
    -/
    sorry
  exists_of_eq := by
    simp only [mul_eq_mul_left_iff, Subtype.exists, exists_prop]
    intro r₁ r₂ h
    use 1
    constructor
    simp [M]
    intro s hs
    have : Prime s.asIdeal := HeightOneSpectrum.prime s
    refine (Ideal.ne_top_iff_one s.asIdeal).mp ?_
    exact Ideal.IsPrime.ne_top'
    left
    have : ((algebraMap R ↥(S.integer K)) r₁ : K) = (algebraMap R ↥(S.integer K)) r₂ := by
      exact congrArg Subtype.val h
    simp at this
    exact this
end

end Set
