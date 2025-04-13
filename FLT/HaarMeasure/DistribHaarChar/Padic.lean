/-
Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Javier López-Contreras
-/
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.HaarMeasure.DistribHaarChar.Basic
import FLT.HaarMeasure.MeasurableSpacePadics

/-!
# The distributive Haar characters of the p-adics

This file computes `distribHaarChar` in the case of the actions of `ℤ_[p]ˣ` on `ℤ_[p]` and of
`ℚ_[p]ˣ` on `ℚ_[p]`.

This lets us know what `volume (x • s)` is in terms of `‖x‖` and `volume s`, when `x` is a
p-adic/p-adic integer and `s` is a set of p-adics/p-adic integers.

## Main declarations

* `distribHaarChar_padic`: `distribHaarChar ℚ_[p]` is the usual p-adic norm on `ℚ_[p]ˣ`.
* `distribHaarChar_padicInt`: `distribHaarChar ℤ_[p]` is constantly `1` on `ℤ_[p]ˣ`.
* `Padic.volume_padic_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℚ_[p]` and
  `s : Set ℚ_[p]`.
* `PadicInt.volume_padicInt_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℤ_[p]` and
  `s : Set ℤ_[p]`.
-/

-- lemma quotient_equiv {R M: Type*} [Ring R] [AddCommGroup M] [Module R M] (p: Submodule R M):
--   Nat.card (M ⧸ p) = Nat.card (AddSubgroup M ⧸ p.toAddSubgroup) := by
--   sorry

open Padic MeasureTheory Measure Metric Set
open scoped Pointwise ENNReal NNReal nonZeroDivisors

variable {p : ℕ} [Fact p.Prime]

lemma nat_enn_of (n: ℕ): (n: ENNReal) = ENNReal.ofNNReal n := by
  norm_cast

lemma nat_nnreal_cast (n: ℕ): (n: ℝ≥0) = ⟨n, by linarith⟩ := by
  norm_cast

lemma subgroup_bot   {G : Type*} [AddGroup G] (H : AddSubgroup G): H.addSubgroupOf ⊤ = ⊤ := by
  simp


private lemma distribHaarChar_padic_padicInt (x : ℤ_[p]⁰) :
    distribHaarChar ℚ_[p] (x : ℚ_[p]ˣ) = ‖(x : ℚ_[p])‖₊ := by
  -- Let `K` be the copy of `ℤ_[p]` inside `ℚ_[p]` and `H` be `xK`.
  let K : AddSubgroup ℤ_[p] := (⊤ : Submodule ℤ_[p] ℤ_[p]).toAddSubgroup
  let H := (x.val • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup
  -- We compute that `volume H = ‖x‖₊ * volume K`.
  -- refine distribHaarChar_eq_of_measure_smul_eq_mul (s := K) (μ := volume) (G := ℚ_[p]ˣ)
  --   (by simp [K, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one])
  --   (by simp [K, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one]) ?_
  -- change volume (H : Set ℚ_[p]) = ‖(x : ℚ_[p])‖₊ * volume (K : Set ℚ_[p])
  -- -- This is true because `H` is a `‖x‖₊⁻¹`-index subgroup of `K`.
  have hHK : H ≤ K := by
    simpa [H, K, -Submodule.smul_le_self_of_tower]
      using (1 : Submodule ℤ_[p] ℚ_[p]).smul_le_self_of_tower (x : ℤ_[p])
  --have : H.FiniteRelIndex K :=
  --  PadicInt.smul_submodule_finiteRelIndex (p := p) (mem_nonZeroDivisors_iff_ne_zero.1 x.2) 1
  have H_relindex_Z : (H.index : ℝ≥0∞) = ‖(x : ℚ_[p])‖₊⁻¹ := by
    have x_nonzero: x.val ≠ 0 := by
      exact nonZeroDivisors.ne_zero x.prop

    have bar := PadicInt.mem_span_pow_iff_le_valuation x x_nonzero (p := p)
    let target_ideal := Ideal.span {↑p ^ x.val.valuation}


    have x_factor := PadicInt.unitCoeff_spec x_nonzero
    norm_cast at x_factor
    unfold H
    nth_rw 1 [x_factor]
    conv =>
      lhs
      arg 1
      arg 1
      arg 1
      equals (Ideal.span {(p: ℤ_[p]) ^ (x.val.valuation)}) =>
        let a := 1
        ext y
        refine ⟨?_, ?_⟩
        . intro hy
          simp at hy
          rw [← Submodule.singleton_set_smul] at hy
          rw [Submodule.mem_singleton_set_smul] at hy
          obtain ⟨m, ⟨m_top, hm⟩⟩ := hy
          rw [Ideal.mem_span_singleton']
          simp at hm
          rw [mul_comm] at hm
          rw [← mul_assoc] at hm
          exact Exists.intro (m * ↑(PadicInt.unitCoeff x_nonzero)) (id (Eq.symm hm))

        . intro hy
          simp
          rw [← Submodule.singleton_set_smul]
          rw [Submodule.mem_singleton_set_smul]
          simp
          simp [mul_assoc]
          simp [mul_comm]
          simp [← mul_assoc]
          simp [mul_comm]

          rw [Ideal.mem_span_singleton'] at hy
          obtain ⟨b, hb⟩ := hy
          use (b * ↑(PadicInt.unitCoeff x_nonzero)⁻¹)
          simp
          exact id (Eq.symm hb)

    have iso := RingHom.quotientKerEquivOfSurjective (f := PadicInt.toZModPow (x.val.valuation) (p := p)) (R := ℤ_[p]) (ZMod.ringHom_surjective (PadicInt.toZModPow (x.val).valuation))
    have card_eq := Nat.card_congr iso.toEquiv
    simp at card_eq

    have ker_equiv := PadicInt.ker_toZModPow (x.val.valuation) (p := p)

    have foo := Ideal.quotEquivOfEq ker_equiv

    have other_card_eq := Nat.card_congr foo.toEquiv
    simp at other_card_eq
    rw [other_card_eq] at card_eq

    have mem_add := Submodule.mem_toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ (x.val).valuation}) (x := 0)

    have wtf: (ℤ_[p] ⧸ (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ (x.val).valuation}))) = (ℤ_[p] ⧸ Ideal.span {(p: ℤ_[p]) ^ (x.val).valuation}) := by
      rfl

    have equiv_z_p_one: (⊤ : AddSubgroup ℤ_[p]).carrier ≃ (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup.carrier := by
      exact {
        toFun := fun y => by
          let z := (y.val • (1 : ℚ_[p]))
          simp [Submodule.toAddSubgroup]
          unfold Submodule.toAddSubmonoid

          dsimp [Submodule.one]
          exact z



        invFun := fun y => by
          unfold K
          simp
          exact QuotientAddGroup.mk (Submodule.topEquiv.symm (R := ℤ_[p]) y.out)
        left_inv := by
          sorry
        right_inv := by
          sorry
      }



    -- have subgroup_equiv: (↥K ⧸ (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ (x.val).valuation})).addSubgroupOf K) ≃ (ℤ_[p] ⧸ Ideal.span {(p: ℤ_[p]) ^ (x.val).valuation}) := by
    --   exact {
    --     toFun := fun y => by
    --       exact Submodule.Quotient.mk (y.out)
    --     invFun := fun y => by
    --       unfold K
    --       simp
    --       exact QuotientAddGroup.mk (Submodule.topEquiv.symm (R := ℤ_[p]) y.out)
    --     left_inv := by
    --       sorry
    --     right_inv := by
    --       sorry
    --   }

    -- have foo: 1 = 1 := by
    --   sorry


    dsimp [AddSubgroup.index]
    rw [wtf]
    rw [card_eq]
    rw [← nnnorm_inv]
    norm_cast
    simp only [Nat.cast_pow, nnnorm, PadicInt.padic_norm_e_of_padicInt, H, K]
    norm_cast
    rw [nat_nnreal_cast]
    rw [Subtype.ext_iff_val]
    simp


    simp_rw [PadicInt.norm_eq_zpow_neg_valuation x_nonzero]
    field_simp
    -- norm_cast



    -- unfold K
    -- simp


    -- unfold K at my_card_eq
    -- rw [my_card_eq]

    -- have foo := Subgroup.index



    -- have top_eq_self := (Submodule.topEquiv (R := ℤ_[p]) (M := ℤ_[p]))
    -- simp [nnnorm]
    -- simp_rw [PadicInt.norm_eq_zpow_neg_valuation x_nonzero]
    -- field_simp
    -- norm_cast

    -- have group_iso := QuotientAddGroup.quotientAddEquivOfEq (G := (⊤: AddSubgroup ℤ_[p]))

    -- --have add_comm := Submodule.Quotient.addCommGroup (Ideal.span {↑(p ^ (x.val).valuation)}) (R := ℤ_[p]) (M := ℤ_[p])




    -- --simp_rw [PadicInt.norm_def]
    -- --rw [Padic.norm_eq_zpow_neg_valuation x_nonzero]




    -- unfold K
    -- unfold AddSubgroup.relindex
    -- simp



    -- rw [PadicInt.ker_toZModPow] at iso
    -- sorry
  rw [← AddSubgroup.relindex_top_right] at H_relindex_Z



  let embed_z: (ℤ_[p] →+ ℚ_[p]) := LinearMap.toSpanSingleton ℤ_[p] ℚ_[p] 1
  have comap_index := AddSubgroup.relindex_comap (f := embed_z) (H := (⊤: AddSubgroup ℚ_[p])) (G' := ℤ_[p]) ⊤

  -- TODO - does this already exist somewhere?
  let my_coe: ℤ_[p] →+ ℚ_[p] := {
    toFun := Subtype.val
    map_zero' := by simp
    map_add' := by simp
  }



  let K_old : AddSubgroup ℚ_[p] := (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup
  let H_old:= (x : ℚ_[p]) • K_old

  have hHK_old : H_old ≤ K_old := by
    simpa [H, K, -Submodule.smul_le_self_of_tower]
      using (1 : Submodule ℤ_[p] ℚ_[p]).smul_le_self_of_tower (x : ℤ_[p])

  have something := AddSubgroup.relindex_comap (H := H_old) (f := my_coe) (K := (⊤ : AddSubgroup ℤ_[p]))

  have : H_old.FiniteRelIndex K_old :=
    PadicInt.smul_submodule_finiteRelIndex (p := p) (mem_nonZeroDivisors_iff_ne_zero.1 x.2) 1

  have map_top: (AddSubgroup.map my_coe ⊤) = K_old := by
    ext a
    unfold my_coe K_old
    refine ⟨?_, ?_⟩
    . intro ha
      simp at ha
      simp
      exact ha
    . intro ha
      simp at ha
      simp
      exact ha

  have map_h_old: (AddSubgroup.comap my_coe H_old) = H := by
    ext a
    unfold my_coe H_old H K_old
    refine ⟨?_, ?_⟩
    . intro ha
      simp at ha
      simp
      rw [Submodule.one_eq_span] at ha
      sorry

      --exact ha
    . intro ha
      simp at ha
      simp
      sorry
      --exact ha

  rw [map_top] at something
  rw [map_h_old] at something

  rw [something] at H_relindex_Z

  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := K_old) (μ := volume) (G := ℚ_[p]ˣ)
    (by simp [K_old, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one])
    (by simp [K_old, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one]) ?_
  change volume (H_old : Set ℚ_[p]) = ‖(x : ℚ_[p])‖₊ * volume (K_old : Set ℚ_[p])


  -- simp [my_coe] at something
  -- simp [AddSubgroup.comap] at something

  -- have H_relindex_Z_old : (H_old.relindex K_old : ℝ≥0∞) = ‖(x : ℚ_[p])‖₊⁻¹ := by
  --   dsimp [AddSubgroup.relindex, AddSubgroup.index]



  --have comap_index := AddSubgroup.relindex_comap (f := LinearMap.toSpanSingleton ℤ_[p] ℚ_[p] 1) (H := (⊤: ↥(Submodule.toAddSubgroup 1))) (G := (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup)

  --have top_index_k: (⊤: AddSubgroup ℤ_[p]).relindex ((1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup) = 1 := by
  --  sorry

  rw [← index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup hHK_old, H_relindex_Z, ENNReal.coe_inv,
    ENNReal.mul_inv_cancel_left]
  · simp
  · simp
  · simp
  · simpa [H_old, K_old, Padic.submodule_one_eq_closedBall]
      using measurableSet_closedBall.const_smul (x : ℚ_[p]ˣ)
  · simpa [K_old, Padic.submodule_one_eq_closedBall] using measurableSet_closedBall

/-- The distributive Haar character of the action of `ℚ_[p]ˣ` on `ℚ_[p]` is the usual p-adic norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℚ_[p]` and `s : Set ℚ_[p]`.
See `Padic.volume_padic_smul` -/
@[simp]
lemma distribHaarChar_padic (x : ℚ_[p]ˣ) : distribHaarChar ℚ_[p] x = ‖(x : ℚ_[p])‖₊ := by
  -- Write the RHS as the application of a monoid hom `g`.
  let g : ℚ_[p]ˣ →* ℝ≥0 := {
    toFun := fun x => ‖(x : ℚ_[p])‖₊
    map_one' := by simp
    map_mul' := by simp
  }
  revert x
  suffices distribHaarChar ℚ_[p] = g by simp [this, g]
  -- By density of `ℤ_[p]⁰` inside `ℚ_[p]ˣ`, it's enough to check that `distribHaarChar ℚ_[p]` and
  -- `g` agree on `ℤ_[p]⁰`.
  refine MonoidHom.eq_of_eqOn_dense (PadicInt.closure_nonZeroDivisors_padicInt (p := p)) ?_
  -- But this is what we proved in `distribHaarChar_padic_padicInt`.
  simp only [eqOn_range, g]
  ext x
  simp [distribHaarChar_padic_padicInt]

@[simp]
lemma Padic.volume_padic_smul (x : ℚ_[p]) (s : Set ℚ_[p]) : volume (x • s) = ‖x‖₊ * volume s := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [(finite_zero.subset s.zero_smul_set_subset).measure_zero]
  · lift x to ℚ_[p]ˣ using hx.isUnit
    rw [← distribHaarChar_padic, distribHaarChar_mul, Units.smul_def]

@[simp] lemma Padic.volume_padicInt_smul (x : ℤ_[p]) (s : Set ℚ_[p]) :
    volume (x • s) = ‖x‖₊ * volume s := by simpa [-volume_padic_smul] using volume_padic_smul x s

@[simp] lemma PadicInt.volume_padicInt_smul (x : ℤ_[p]) (s : Set ℤ_[p]) :
    volume (x • s) = ‖x‖₊ * volume s := by
  simpa [-volume_padicInt_smul, ← image_coe_smul_set] using Padic.volume_padicInt_smul x ((↑) '' s)

/-- The distributive Haar character of the action of `ℤ_[p]ˣ` on `ℤ_[p]` is the constant `1`.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℤ_[p]` and `s : Set ℤ_[p]`.
See `PadicInt.volume_padicInt_smul` -/
@[simp]
lemma distribHaarChar_padicInt (x : ℤ_[p]ˣ) : distribHaarChar ℤ_[p] x = 1 :=
  -- We compute `distribHaarChar ℤ_[p]` by lifting everything to `ℚ_[p]`.
  distribHaarChar_eq_of_measure_smul_eq_mul (s := univ) (μ := volume) (by simp) (measure_ne_top _ _)
    (by simp [PadicInt.volume_padicInt_smul])
