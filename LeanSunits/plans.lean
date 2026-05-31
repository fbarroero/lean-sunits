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
    refine Ideal.IsPrime.mul_notMem ?_ ha hb
    exact v.isPrime
  one_mem' := by
    simp only [Submodule.carrier_eq_coe, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true, and_true]
    intro v hv
    refine (Ideal.ne_top_iff_one v.asIdeal).mp ?_
    exact Ideal.IsPrime.ne_top'
}

theorem foo : S.MultiplicativeSet ≤ nonZeroDivisors R := fun _ h ↦ h.2

lemma Ideal.pow_eq_bot {R : Type*} (n : ℕ) [Semiring R] {I : Ideal R} [NoZeroDivisors R] :
    I ^ (n + 1) = ⊥ ↔ I = ⊥ := by
  induction n with
  | zero => simp [Submodule.pow_one]
  | succ n ih =>
    constructor
    · intro h
      rw [Submodule.pow_succ, Ideal.mul_eq_bot] at h
      rcases h with h | h
      · rwa [← ih]
      · exact h
    · simp_all

open IsLocalization in
theorem IsLocalization.coeSubmodule_pow {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
  (I : Ideal R) (n : ℕ):
    coeSubmodule S (I ^ n) = coeSubmodule S I ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Submodule.pow_succ, ih, IsLocalization.coeSubmodule_mul]


--- We prove that the S.integers are indeed a localization. Should probably not be here but in Sinteger.lean?
set_option maxHeartbeats 500000 in
lemma sur [Fact (Monoid.IsTorsion (ClassGroup R))] :
    ∀ z : S.integer K, ∃ x : R × S.MultiplicativeSet,
    z * (algebraMap R (S.integer K)) x.2 = (algebraMap R (S.integer K)) x.1 := by
  intro r
  simp only [Prod.exists, Subtype.exists, exists_prop]

  -- relevant stuff: https://math.stackexchange.com/questions/3366605/two-different-ways-of-presenting-the-ring-of-s-integers?rq=1
  --https://math.stackexchange.com/questions/3448941/is-ring-of-s-integers-a-dedekind-domain

  -- We know that v(r) ≥ 0 for all ν ∉ S.
  --useless for the moment
  have h_outside : ∀ v ∉ S, v.valuation K r ≤ 1 := fun _ h ↦ integer_valuation_le_one S K r h

 /-  let T' := {T | ∀ v ∈ S \ T, v.valuation K (r : K) ≤ 1}
  have : T'.Finite := by sorry
  let T := this.toFinset
   -/

  --let T : (Finset <| HeightOneSpectrum R) := ⟨sorry, sorry ⟩

  -- There exists a finite subset T of S such that v(r) ≥ 0 for all v ∈ S \ T. this is where the denominator of r lies
  classical
  let Tset : Set (HeightOneSpectrum R) := HeightOneSpectrum.Support R (r : K)
  have hTset : Tset.Finite := by
    simpa [Tset] using (HeightOneSpectrum.Support.finite (R := R) (K := K) (k := (r : K)))
  let T : Finset (HeightOneSpectrum R) := hTset.toFinset
  have hT : ∀ v ∈ S \ T, v.valuation K (r : K) ≤ 1 := by
    intro v hv
    have hvTset : v ∉ (hTset.toFinset : Set (HeightOneSpectrum R)) := hv.2
    have hvT : v ∉ Tset := by
      intro hv'
      exact hvTset ((hTset.mem_toFinset).2 hv')
    exact le_of_not_gt (by simpa [Tset, HeightOneSpectrum.Support] using hvT)
  have hT_subset : ∀ v ∈ T, v ∈ S := by
    intro v hvT
    by_contra hvS
    have hvSupport : v ∈ Tset := (hTset.mem_toFinset).1 hvT
    exact not_lt_of_ge (h_outside v hvS) (by simpa [Tset, HeightOneSpectrum.Support] using hvSupport)
  have : ∃ T : (Finset <| HeightOneSpectrum R), ∀ v ∈ S \ T, v.valuation K (r : K) ≤ 1 := ⟨T, hT⟩
  let I : Ideal R := ∏ v ∈ T, v.asIdeal

  -- Show that v(I) = 1 for all v ∈ T.
  have h_count : ∀ v ∈ T, FractionalIdeal.count K v I = 1 := by
    intro v hv
    change FractionalIdeal.count K v (↑(∏ w ∈ T, w.asIdeal) : FractionalIdeal R⁰ K) = 1
    rw [show (↑(∏ w ∈ T, w.asIdeal) : FractionalIdeal R⁰ K) =
        ∏ w ∈ T, (w.asIdeal : FractionalIdeal R⁰ K) by
      exact _root_.map_prod (FractionalIdeal.coeIdealHom R⁰ K)
        (fun w : HeightOneSpectrum R => w.asIdeal) T]
    rw [FractionalIdeal.count_prod]
    · simp [FractionalIdeal.count_maximal, hv]
    · intro w hw
      exact FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  have hI_ne_zero : I ≠ 0 := by
    intro hI
    rw [hI] at h_count
    simp_all only [mem_diff, SetLike.mem_coe, and_imp, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot, I]
    obtain ⟨val, property⟩ := r
    obtain ⟨w, h_1⟩ := this
    simp_all only
    rw [bot_eq_zero, Finset.prod_eq_zero_iff] at hI
    obtain ⟨v, hvT, hvI⟩ := hI
    rw [← bot_eq_zero] at hvI
    exact v.3 hvI
  -- There exists n > 0 such that I^n is principal.
  have : ∃ n : ℕ, 0 < n ∧ (I ^ n).IsPrincipal := by
    let h : Monoid.IsTorsion (ClassGroup R) := Fact.out
    let I' : (FractionalIdeal (nonZeroDivisors R) K)ˣ :={
      val:= (FractionalIdeal.coeIdeal I)
      inv := (FractionalIdeal.coeIdeal I)⁻¹
      val_inv := by aesop
      inv_val := by aesop
    }
    let I₀ := ClassGroup.mk K I'
    have : IsOfFinOrder I₀ := h I₀
    rw [isOfFinOrder_iff_pow_eq_one] at this
    obtain ⟨n, hn, hI'⟩ := this
    refine ⟨n, hn, ?_⟩
    simp [I₀] at hI'
    have : ClassGroup.mk K I' ^ n = ClassGroup.mk K (I' ^ n) := (MonoidHom.map_pow (ClassGroup.mk K) I' n).symm
    rw [this, ClassGroup.mk_eq_one_iff] at hI'
    simp only [Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow, FractionalIdeal.coe_coeIdeal,
      I'] at hI'
    rw [← IsLocalization.coeSubmodule_pow] at hI'
    simp_all

  -- There exists α such that I^n = (α)
  obtain ⟨n, hn, ⟨α, hα⟩⟩ := this

  -- This α : R has to satisfy v(α) ≥ 1 if v ∈ T [and v(α) ≥ 0 elsewise].
  have h1 : ∀ v ∈ T, v.valuation K (algebraMap R K α) < 1 := by
    intro v hv
    rw [valuation_lt_one_iff_mem]
    rw [← Ideal.span_singleton_le_iff_mem]
    change R ∙ α ≤ v.asIdeal
    rw [← hα]
    have hI_le : (∏ w ∈ T, w.asIdeal) ≤ v.asIdeal := by
      exact (Ideal.prod_le_inf (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)).trans
        (Finset.inf_le hv)
    exact (Ideal.pow_le_self (Nat.ne_of_gt hn)).trans hI_le

  have hm : ∃ m : ℕ, ∀ v ∈ T, v.valuation K ((algebraMap R K α ^ m) * r) ≤ 1 := by
    have hα_ne_zero : α ≠ 0 := by
      intro hα_zero
      apply hI_ne_zero
      simp [hα_zero] at hα
      rw [Ideal.zero_eq_bot, ← Ideal.pow_eq_bot (n - 1), ← hα]
      congr
      omega
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
    have hαK_ne_zero : (algebraMap R K α) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_eq_zero_iff R K).not.mpr hα_ne_zero
    have ha : a ≠ 0 := by
      exact (Valuation.ne_zero_iff (v.valuation K)).2 hαK_ne_zero
    have hloga_lt : WithZero.log a < 0 := by
      exact (WithZero.log_lt_log ha one_ne_zero).2 (by
        simpa [a] using h1 v hv)
    have hloga_le : WithZero.log a ≤ (-1 : ℤ) := by
      omega
    have hlogb_le : WithZero.log b ≤ (m : ℤ) := by
      have hsingle :
          (WithZero.log (v.valuation K (r : K))).toNat ≤ m := by
        exact Finset.single_le_sum
          (s := T) (f := fun w : HeightOneSpectrum R =>
            (WithZero.log (w.valuation K (r : K))).toNat)
          (fun w hw => Nat.zero_le _) hv
      have htoNat : WithZero.log b ≤ ((WithZero.log b).toNat : ℤ) := Int.self_le_toNat _
      exact htoNat.trans (by
        dsimp [b, m] at hsingle ⊢
        exact_mod_cast hsingle)
    have hlog : WithZero.log (a ^ m * b) ≤ 0 := by
      rw [WithZero.log_mul (pow_ne_zero m ha) hb, WithZero.log_pow]
      calc
        m • WithZero.log a + WithZero.log b ≤ m • (-1 : ℤ) + (m : ℤ) := by
          exact add_le_add (nsmul_le_nsmul_right hloga_le m) hlogb_le
        _ = 0 := by simp
    rw [← WithZero.log_le_log (mul_ne_zero (pow_ne_zero m ha) hb) one_ne_zero]
    simpa using hlog

  obtain ⟨m, hm⟩ := hm

  have hβ : ∃ β : R, (algebraMap R K β) = ((algebraMap R K α ^ m) * r) := by
    have hx : ∀ v : HeightOneSpectrum R, v.valuation K ((algebraMap R K α ^ m) * r) ≤ 1 := by
      intro v
      by_cases hvT : v ∈ T
      · exact hm v hvT
      · have hrle : v.valuation K r ≤ 1 := by
          by_cases hvS : v ∈ S
          · exact hT v ⟨hvS, hvT⟩
          · exact h_outside v hvS
        have hαle : v.valuation K ((algebraMap R K α) ^ m) ≤ 1 := by
          simpa [map_pow] using (v.valuation_le_one (K := K) (α ^ m))
        calc
          v.valuation K ((algebraMap R K α ^ m) * r)
              = v.valuation K ((algebraMap R K α) ^ m) * v.valuation K r := by
                  simp [Valuation.map_mul]
          _ ≤ 1 * 1 := mul_le_mul' hαle hrle
          _ = 1 := by simp
    simpa [Set.mem_range] using
      (HeightOneSpectrum.mem_integers_of_valuation_le_one (R := R) (K := K)
        ((algebraMap R K α ^ m) * r) hx)

  obtain ⟨β, hβ⟩ := hβ
  use β
  use α ^ m
  constructor
  · refine Submonoid.pow_mem S.MultiplicativeSet ?_ m
    simp [MultiplicativeSet]
    --simp at hα
    constructor
    · intro v
      contrapose
      intro hv




      --rw [← @intValuation_eq_one_iff]
      simp_all only [mem_diff, SetLike.mem_coe, and_imp, Submodule.zero_eq_bot, ne_eq, map_mul, map_pow, I]
      obtain ⟨val, property⟩ := r
      obtain ⟨w, h⟩ := this
      simp_all only
      have hspan_le : R ∙ α ≤ v.asIdeal := by
        exact (Ideal.span_singleton_le_iff_mem v.asIdeal).2 hv
      have hpow_le : (∏ w ∈ T, w.asIdeal) ^ n ≤ v.asIdeal := by
        rw [hα]
        exact hspan_le
      have hI_le : (∏ w ∈ T, w.asIdeal) ≤ v.asIdeal :=
        Ideal.IsPrime.le_of_pow_le hpow_le
      obtain ⟨w, hwT, hwle⟩ :=
        (Ideal.IsPrime.prod_le (s := T) (f := fun w : HeightOneSpectrum R => w.asIdeal)
          v.isPrime).1 hI_le
      have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top'
      have hw_eq : w = v := by
        exact HeightOneSpectrum.ext (Ideal.IsMaximal.eq_of_le w.isMaximal
          hv_ne_top hwle)
      exact hT_subset v (by simpa [hw_eq] using hwT)
    · intro rfl
      apply hI_ne_zero

      simp at hα
      rw [Ideal.zero_eq_bot, ← Ideal.pow_eq_bot (n - 1), ← hα]
      congr
      omega
  · simp
    ext
    simpa [mul_comm, mul_left_comm, mul_assoc] using hβ.symm



--#count_heartbeats in
instance inst [Fact (Monoid.IsTorsion (ClassGroup R))] :
    IsLocalization S.MultiplicativeSet <| S.integer K where
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
    · simp only [MultiplicativeSet, Submodule.carrier_eq_coe, Submonoid.mem_mk,
      Subsemigroup.mem_mk, mem_inter_iff, mem_iInter, mem_compl_iff, SetLike.mem_coe,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true, and_true]
      intro s hs
      exact (Ideal.ne_top_iff_one s.asIdeal).mp Ideal.IsPrime.ne_top'
    · left
      have : ((algebraMap R (S.integer K)) r₁ : K) = (algebraMap R (S.integer K)) r₂ :=
        congrArg Subtype.val h
      simp_all

-- S.integers are a Dedekind domain.
instance isDedekindDomain [Fact (Monoid.IsTorsion (ClassGroup R))] : IsDedekindDomain (S.integer K) := by
  have : IsLocalization S.MultiplicativeSet ↥(S.integer K) := inst S K
  exact  IsLocalization.isDedekindDomain _ (foo S) _



end
end Set
