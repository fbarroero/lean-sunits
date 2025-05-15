import Mathlib

namespace Set

noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R)
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

--- MultiplicativeSet is the multiplicative submonoid consisting of all r ∈ R such that ν(r) ≥ 0 for all ν ∉ S. Note that we allow infinite sets S, for which M would contain 0 unless we intersect with (nonZeroDivisors R).

def MultiplicativeSet : Submonoid R := {
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

theorem foo : S.MultiplicativeSet ≤ nonZeroDivisors R := fun _ h ↦ h.2

--- We prove that the S.integers are indeed a localization. Should probably not be here but in Sinteger.lean?

--#count_heartbeats in
instance : IsLocalization S.MultiplicativeSet <| S.integer K where
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
      intro v hv
      have hmem : r ∉ v.asIdeal := by simp_all
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_apply]
      --make a PR with this?

      have := v.intValuation_le_one r
      rw [le_iff_lt_or_eq] at this
      have : ¬ v.intValuationDef r < 1 := by
        rw [v.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]
        exact hmem
      simp_all
    use unitEquivUnitsInteger S K ⟨x, this⟩
    rfl -/
  surj' := by
    intro r
    simp only [Prod.exists, Subtype.exists, exists_prop]
    -- relevant stuff: https://math.stackexchange.com/questions/3366605/two-different-ways-of-presenting-the-ring-of-s-integers?rq=1
    --https://math.stackexchange.com/questions/3448941/is-ring-of-s-integers-a-dedekind-domain

    -- We know that v(r) ≥ 0 for all ν ∉ S.
    have : ∀ v ∉ S, v.valuation K r ≤ 1 := by
      exact fun v a ↦ integer_valuation_le_one S K r a

    -- There exists a finite subset T of S such that v(r) ≥ 0 for all ν ∈ S \ T.
    have : ∃ T : (Finset <| HeightOneSpectrum R), ∀ v ∈ S \ T, v.valuation K (↑r : K) ≤ 1 := by
      sorry

    let ⟨T, hT⟩ := this
    let I : Ideal R := ∏ v ∈ T, v.asIdeal

    -- Show that v(I) = 1 for all v ∈ T.
    have : ∀ v ∈ T, FractionalIdeal.count K v I = 1 := by
      sorry

    -- There exists n > 0 such that I^n is principal.
    have : ∃ n : ℕ, 0 < n ∧ (I^n).IsPrincipal := by
      sorry
    -- NumberField.RingOfIntegers.instFintypeClassGroup

    -- There exists α such that I^n = (α)
    obtain ⟨n, hn, ⟨α,hα⟩⟩ := this

    -- This α : R has to satisfy v(α) ≥ 1 if v ∈ T [and v(α) ≥ 0 elsewise].
    have : ∀ v ∈ T, v.valuation K (algebraMap R K α) < 1 := by
      sorry

    have : ∃ m : ℕ, ∀ v ∈ T, v.valuation K ((algebraMap R K α^m) * r) ≤ 1 := by
      sorry

    obtain ⟨m, hm⟩ := this

    have : ∃ β : R, (algebraMap R K β) = ((algebraMap R K α^m) * r) := by
      sorry

    obtain ⟨β, hβ⟩ := this

    use β

    use α^m

    constructor
    ·
      sorry
    ·
      simp [hβ]
      sorry

  exists_of_eq := by
    simp only [mul_eq_mul_left_iff, Subtype.exists, exists_prop]
    intro r₁ r₂ h
    use 1
    constructor
    · simp only [MultiplicativeSet, Submodule.carrier_eq_coe, Submonoid.mem_mk,
      Subsemigroup.mem_mk, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true, and_true]
      intro s hs
      exact (Ideal.ne_top_iff_one s.asIdeal).mp Ideal.IsPrime.ne_top'
    · left
      have : ((algebraMap R ↥(S.integer K)) r₁ : K) = (algebraMap R ↥(S.integer K)) r₂ := congrArg Subtype.val h
      simp only [SubalgebraClass.coe_algebraMap, IsFractionRing.coe_inj] at this
      exact this

-- S.integers are a Dedekind domain.
instance isDedekindDomain : IsDedekindDomain (S.integer K) := IsLocalization.isDedekindDomain _ (foo S) _



end
end Set
