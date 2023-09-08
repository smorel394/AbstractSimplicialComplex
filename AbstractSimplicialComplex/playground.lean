import Mathlib 


noncomputable def SuccOrdertoAntisymmetrization {s : Preorder α} (hsucc : @SuccOrder α s) : @SuccOrder (Antisymmetrization α s.le)
(@PartialOrder.toPreorder _ (@instPartialOrderAntisymmetrizationLeToLEInstIsPreorderLeToLE α s)) where
succ := fun x => toAntisymmetrization s.le (hsucc.succ (ofAntisymmetrization s.le x))
le_succ := fun x => by rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), toAntisymmetrization_le_toAntisymmetrization_iff]
                       rw [toAntisymmetrization_ofAntisymmetrization]
                       exact hsucc.le_succ _ 
max_of_succ_le := fun hx => by rename_i x
                               intro y hyx
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x)] at hyx hx ⊢ 
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le y)] at hyx ⊢
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff] at hyx hx ⊢
                               rw [toAntisymmetrization_ofAntisymmetrization] at hx 
                               exact hsucc.max_of_succ_le hx hyx 
succ_le_of_lt := fun hxy => by rename_i x y
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x), ←(toAntisymmetrization_ofAntisymmetrization s.le y)]
                                 at hxy ⊢
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff]
                               rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy
                               rw [toAntisymmetrization_ofAntisymmetrization]
                               exact hsucc.succ_le_of_lt hxy
le_of_lt_succ := fun hxy => by rename_i x y 
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le x)] at hxy ⊢ 
                               rw [←(toAntisymmetrization_ofAntisymmetrization s.le y)]
                               rw [toAntisymmetrization_le_toAntisymmetrization_iff]  
                               rw [toAntisymmetrization_lt_toAntisymmetrization_iff] at hxy 
                               exact hsucc.le_of_lt_succ hxy 



#exit 

open scoped TensorProduct 


variable {R : Type _} [CommSemiring R]
  {A B : Type _} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (I : Ideal B)

def AlgHom.Quotient : B →ₐ (@Ideal.instHasQuotientIdealToSemiringToCommSemiring B _).quotient' I := sorry with 
  commutes' := sorry 

example :
  (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R =
    LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  let J : Ideal (A ⊗[R] B) := RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) (Ideal.Quotient.mk I))


#exit 


example :
  (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R =
    LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  let J : Ideal (A ⊗[R] B) := {
    carrier := LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R)))
    add_mem' := fun {x} {y} hx hy  ↦ Submodule.add_mem _ hx hy
    zero_mem' := by
      simp only [SetLike.mem_coe]
      apply zero_mem
    smul_mem' := fun x y ↦ by
      simp only [SetLike.mem_coe]
      rintro ⟨y, rfl⟩
      induction x using TensorProduct.induction_on with 
      | zero =>
          rw [zero_smul]
          apply zero_mem
      | tmul a b =>
          induction y using TensorProduct.induction_on with
          | zero =>
              rw [map_zero]
              apply zero_mem
          | tmul x y =>
              simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype, smul_eq_mul, tmul_mul_tmul]
              suffices h : b * ↑y ∈ Submodule.restrictScalars R I
              use (a * x) ⊗ₜ[R] ⟨b * ↑y, h⟩
              rfl
              simp only [Submodule.coe_restrictScalars, Submodule.restrictScalars_mem]
              apply Ideal.mul_mem_left
              exact y.prop
          | add x y hx hy =>
              rw [map_add, smul_add]
              exact Submodule.add_mem _ hx hy
      | add x x' hx hx' =>
          rw [add_smul]
          exact Submodule.add_mem _ hx hx' }
  suffices : Ideal.map includeRight I = J 
  rw [this]
  rfl
  -- Ideal.map includeRight I = J
  apply le_antisymm
  · rw [Ideal.map, Ideal.span_le]
    rintro x ⟨b, hb, rfl⟩
    simp only [includeRight_apply, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk,
      SetLike.mem_coe, LinearMap.mem_range]
    suffices hb' : _
    use 1 ⊗ₜ[R] ⟨b, hb⟩
    rfl
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype]
        suffices : a ⊗ₜ[R] (b : B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] (b : B))
        rw [this]
        apply Ideal.mul_mem_left
        apply Ideal.mem_map_of_mem
        exact Submodule.coe_mem b
        simp only [Submodule.coe_restrictScalars, tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Ideal.add_mem _ hx hy
