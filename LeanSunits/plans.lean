import Mathlib

namespace Set

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

universe u v

variable
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R)
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/- MultiplicativeSet is the multiplicative submonoid consisting of all r ∈ R such that ν(r) ≥ 0 for
all ν ∉ S. Note that we allow infinite sets S, for which M would contain 0 unless we intersect with
(nonZeroDivisors R). -/

def Submonoid : Submonoid R := {
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∉ S), (v.asIdeal.carrier)ᶜ) ∩ (nonZeroDivisors R)
  mul_mem' := by
    rintro _ _ ⟨ha, ha0⟩ ⟨hb, hb0⟩
    simp only [mem_iInter, mem_inter_iff] at ha hb ⊢
    exact ⟨fun v hv ↦ v.isPrime.mul_notMem (ha v hv) (hb v hv), (nonZeroDivisors R).mul_mem ha0 hb0⟩
  one_mem' := by simpa using fun i (_ : i ∉ S) ↦ i.asIdeal.one_notMem
}

-- PR this to Mathlib soon
lemma Ideal.pow_eq_bot {R : Type*} (n : ℕ) [Semiring R] {I : Ideal R} [NoZeroDivisors R] :
    I ^ (n + 1) = ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ eq_bot_iff.2 fun x hx ↦ eq_zero_of_pow_eq_zero (n := n + 1) <| by
    simpa [h] using I.pow_mem_pow hx (n + 1), fun h ↦ by simp [h]⟩

--- We prove that the S.integers are indeed a localization. Should probably not be here but in Sinteger.lean?
--set_option maxHeartbeats 500000 in

  -- relevant stuff: https://math.stackexchange.com/questions/3366605/two-different-ways-of-presenting-the-ring-of-s-integers?rq=1
  --https://math.stackexchange.com/questions/3448941/is-ring-of-s-integers-a-dedekind-domain
lemma sur [Fact (Monoid.IsTorsion (ClassGroup R))] :
    ∀ z : S.integer K, ∃ x : R × S.Submonoid,
    z * (algebraMap R (S.integer K)) x.2 = (algebraMap R (S.integer K)) x.1 := by
  intro r
  simp only [Prod.exists, Subtype.exists, exists_prop]
  --classical
  -- We know that v(r) ≥ 0 for all ν ∉ S.
  have h_outside : ∀ v ∉ S, v.valuation K r ≤ 1 := fun _ h ↦ integer_valuation_le_one S K r h
  let T : Finset (HeightOneSpectrum R) :=
    (HeightOneSpectrum.Support.finite (R := R) (K := K) (k := (r : K))).toFinset
  have hT : ∀ v ∈ S \ T, v.valuation K (r : K) ≤ 1 := fun v hv ↦
    le_of_not_gt (by simpa [T, HeightOneSpectrum.Support] using hv.2)
  have hT_subset : ∀ v ∈ T, v ∈ S := fun v hvT ↦ by
    by_contra hvS
    exact not_lt_of_ge (h_outside v hvS) (by
      simpa [T, HeightOneSpectrum.Support] using hvT)
  let I : Ideal R := ∏ v ∈ T, v.asIdeal

  have hI_ne_zero : I ≠ 0 := by
    change (∏ v ∈ T, v.asIdeal) ≠ 0
    simpa only [Finset.prod_ne_zero_iff, bot_eq_zero] using fun v (_ : v ∈ T) ↦ v.ne_bot
  -- There exist n > 0 and α such that I^n = (α).
  obtain ⟨n, hn, ⟨α, hα⟩⟩ : ∃ n : ℕ, 0 < n ∧ (I ^ n).IsPrincipal := by
    let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne_zero⟩
    obtain ⟨n, hn, hI'⟩ := isOfFinOrder_iff_pow_eq_one.1
      ((Fact.out : Monoid.IsTorsion (ClassGroup R)) (ClassGroup.mk0 I₀))
    refine ⟨n, hn, ?_⟩
    rw [← MonoidHom.map_pow ClassGroup.mk0 I₀ n, ClassGroup.mk0_eq_one_iff] at hI'
    simpa [I₀] using hI'
  have hα_ne_zero : α ≠ 0 := by
    rintro rfl
    apply hI_ne_zero
    simp at hα
    rw [Ideal.zero_eq_bot, ← Ideal.pow_eq_bot (n - 1), ← hα]
    congr
    omega

  -- This α : R has to satisfy v(α) ≥ 1 if v ∈ T [and v(α) ≥ 0 elsewise].
  have h1 : ∀ v ∈ T, v.valuation K (algebraMap R K α) < 1 := by
    intro v hv
    rw [valuation_lt_one_iff_mem, ← Ideal.span_singleton_le_iff_mem]
    change R ∙ α ≤ v.asIdeal
    rw [← hα]
    exact (Ideal.pow_le_self hn.ne').trans <|
      (Ideal.prod_le_inf (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)).trans
        (Finset.inf_le hv)

  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v ∈ T,
      v.valuation K ((algebraMap R K α ^ m) * r) ≤ 1 := by
    let m : ℕ := ∑ v ∈ T, (WithZero.log (v.valuation K (r : K))).toNat
    refine ⟨m, ?_⟩
    intro v hv
    let a : WithZero (Multiplicative ℤ) := v.valuation K (algebraMap R K α)
    let b : WithZero (Multiplicative ℤ) := v.valuation K (r : K)
    have hval :
        v.valuation K ((algebraMap R K α ^ m) * r) = a ^ m * b := by
      simp [a, b, Valuation.map_mul]
    rw [hval]
    by_cases hb : b = 0
    · simp [hb]
    have ha : a ≠ 0 := by
      simpa [a, Valuation.ne_zero_iff] using
        (FaithfulSMul.algebraMap_eq_zero_iff R K).not.mpr hα_ne_zero
    have hloga_le : WithZero.log a ≤ (-1 : ℤ) := by
      have : WithZero.log a < 0 := by
        simpa using (WithZero.log_lt_log ha one_ne_zero).2 (by simpa [a] using h1 v hv)
      omega
    have hlogb_le : WithZero.log b ≤ (m : ℤ) := by
      refine (Int.self_le_toNat _).trans ?_
      dsimp [b, m]
      exact_mod_cast Finset.single_le_sum
        (s := T) (f := fun w : HeightOneSpectrum R =>
          (WithZero.log (w.valuation K (r : K))).toNat)
        (fun w hw => Nat.zero_le _) hv
    have hlog : WithZero.log (a ^ m * b) ≤ 0 := by
      rw [WithZero.log_mul (pow_ne_zero m ha) hb, WithZero.log_pow]
      simpa using add_le_add (nsmul_le_nsmul_right hloga_le m) hlogb_le
    rw [← WithZero.log_le_log (mul_ne_zero (pow_ne_zero m ha) hb) one_ne_zero]
    simpa using hlog

  obtain ⟨β, hβ⟩ : ∃ β : R, (algebraMap R K β) = ((algebraMap R K α ^ m) * r) := by
    have hx : ∀ v : HeightOneSpectrum R, v.valuation K ((algebraMap R K α ^ m) * r) ≤ 1 := by
      intro v
      by_cases hvT : v ∈ T
      · exact hm v hvT
      · have hrle : v.valuation K r ≤ 1 := by
          by_cases hvS : v ∈ S
          · exact hT v ⟨hvS, hvT⟩
          · exact h_outside v hvS
        simpa [Valuation.map_mul] using
          mul_le_mul' (by simpa [map_pow] using (v.valuation_le_one (K := K) (α ^ m))) hrle
    simpa [Set.mem_range] using
      (HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) (K := K)
        ((algebraMap R K α ^ m) * r) hx)
  refine ⟨β, α ^ m, ?_, ?_⟩
  · refine Submonoid.pow_mem S.Submonoid ?_ m
    simp [Submonoid]
    refine ⟨?_, hα_ne_zero⟩
    intro v hvS hvα
    obtain ⟨w, hwT, hwle⟩ :=
      (Ideal.IsPrime.prod_le (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)
        v.isPrime).1 <| Ideal.IsPrime.le_of_pow_le (by
          rw [hα]
          exact (Ideal.span_singleton_le_iff_mem v.asIdeal).2 hvα)
    have hw_eq : w = v :=
      HeightOneSpectrum.ext (Ideal.IsMaximal.eq_of_le w.isMaximal v.isPrime.ne_top' hwle)
    exact hvS (hT_subset v (by simpa [hw_eq] using hwT))
  · ext
    simpa [mul_comm, mul_left_comm, mul_assoc] using hβ.symm



--#count_heartbeats in
instance inst [Fact (Monoid.IsTorsion (ClassGroup R))] :
    IsLocalization S.Submonoid <| S.integer K where
  map_units y := by
    obtain ⟨r, hr⟩ := y
    have h₀ : r ≠ 0 := nonZeroDivisors.ne_zero hr.2
    let x : Kˣ := {
      val := algebraMap R K r
      inv := (algebraMap R K r)⁻¹
      val_inv := by simp [h₀]
      inv_val := by simp [h₀]
    }
    have : x ∈ S.unit K := by
      intro v hv
      have hmem : r ∉ v.asIdeal := by
        have := hr.1
        simp_all
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      simp_all
    use unitEquivUnitsInteger S K ⟨x, this⟩
    rfl
  surj z := sur S K z
  exists_of_eq := by
    simp only [mul_eq_mul_left_iff, Subtype.exists, exists_prop]
    intro r₁ r₂ h
    use 1
    constructor
    · simp only [Submonoid, Submodule.carrier_eq_coe, Submonoid.mem_mk,
      Subsemigroup.mem_mk, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true, and_true]
      intro s hs
      exact (Ideal.ne_top_iff_one s.asIdeal).mp Ideal.IsPrime.ne_top'
    · left
      have : ((algebraMap R (S.integer K)) r₁ : K) = (algebraMap R (S.integer K)) r₂ :=
        congrArg Subtype.val h
      simp_all

-- S.integers are a Dedekind domain.
instance isDedekindDomain [Fact (Monoid.IsTorsion (ClassGroup R))] : IsDedekindDomain (S.integer K) :=
  --have : IsLocalization S.Submonoid ↥(S.integer K) := inst S K
  IsLocalization.isDedekindDomain _ (fun _ h ↦ h.2 : S.Submonoid ≤ nonZeroDivisors R) _



end
end Set
