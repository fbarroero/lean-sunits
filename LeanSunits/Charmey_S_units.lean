import Mathlib
/-!
# Example file for S-units
-/

open IsDedekindDomain

/- Define a bunch of variables. -/
variable {R : Type} [CommRing R] [IsDedekindDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-!
## Stuff about S-integers
-/

/-- The map `Kˣ → ℤ` given by the valuation `v`.  -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.unitsHom : Kˣ →* Multiplicative ℤ where
  toFun x := WithZero.unzero (v.valuation.ne_zero_of_unit x)
  map_one' := by simp [WithZero.unzero_coe]; rfl
  map_mul' x y := by simp [WithZero.unzero_mul]


theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation x ≤ 1) : x ∈ (algebraMap R K).range := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Ideal R) by
    obtain ⟨z, rfl⟩ := Ideal.span_singleton_le_span_singleton.1 (Ideal.le_of_dvd this)
    use z
    rw [map_mul, mul_comm, mul_eq_mul_left_iff] at hx
    exact (hx.resolve_right fun h => by simp [hd0] at h).symm
  classical
  have ine {r : R} : r ≠ 0 → Ideal.span {r} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp
  rw [← Associates.mk_le_mk_iff_dvd, ← Associates.factors_le, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), WithTop.coe_le_coe, Multiset.le_iff_count]
  rintro ⟨v, hv⟩
  obtain ⟨v, rfl⟩ := Associates.mk_surjective v
  have hv' := hv
  rw [Associates.irreducible_mk, irreducible_iff_prime] at hv
  specialize h ⟨v, Ideal.isPrime_of_prime hv, hv.ne_zero⟩
  simp_rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk', IsDedekindDomain.HeightOneSpectrum.intValuation, ← Valuation.toFun_eq_coe,
    IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hn0, IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hd0, ← WithZero.coe_div,
    ← WithZero.coe_one, WithZero.coe_le_coe, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h

lemma IsDedekindDomain.HeightOneSpectrum.unitsHom_apply (x : Kˣ) :
    v.unitsHom x = v.valuation x.val := by
  simp [unitsHom, WithZero.coe_unzero]

/-- If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of `K` (which is
just `R` itself). -/
lemma set_integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := by
  ext x
  rw[Algebra.mem_bot, Set.mem_range, <- Subalgebra.mem_carrier]
  simp
  constructor
  · intro h
    rw[<-Set.mem_range]
    apply mem_integers_of_valuation_le_one
    tauto
  · intro h
    intro v
    obtain ⟨y,hy⟩ := h
    rw[<- hy]
    rw[IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef]
    apply IsDedekindDomain.HeightOneSpectrum.intValuation_le_one


/-- If `S` is the empty set, then the `S`-units are just `Rˣ`, embedded in `K`. -/
def set_unit_empty_equiv : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).integer K := by
  rw[set_integer_empty]
  apply Algebra.botEquivOfInjective
  sorry
