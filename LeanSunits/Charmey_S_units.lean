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

@[simp]
lemma foo : (One.one : Multiplicative ℤ) = 1 := rfl

/-- The map `Kˣ → ℤ` given by the valuation `v`.  -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.unitsHom : Kˣ →* Multiplicative ℤ where
  toFun x := WithZero.unzero (v.valuation.ne_zero_of_unit x)
  map_one' := by simp [WithZero.unzero_coe]
  map_mul' x y := by simp [WithZero.unzero_mul]

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
    rw [<-Set.mem_range]
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
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
  --apply Algebra.botEquivOfInjective
  sorry
