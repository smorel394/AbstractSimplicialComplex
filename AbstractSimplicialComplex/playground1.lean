import Mathlib.Tactic 
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct


section prelim

variable {R : Type _} [CommSemiring R]
  {A : Type _} [Semiring A] [Algebra R A] 
variable {M : Type _} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] 

lemma ModuleAction.toLinearMap_add (a b : A) :
DistribMulAction.toLinearMap R M (a + b) = (DistribMulAction.toLinearMap R M a) + (DistribMulAction.toLinearMap R M b) := by 
  ext x 
  simp only [DistribMulAction.toLinearMap_apply, LinearMap.add_apply]
  rw [add_smul]


lemma ModuleAction.toLinearMap_smul (r : R) (a : A) :
DistribMulAction.toLinearMap R M (r • a) = r • (DistribMulAction.toLinearMap R M a) := by 
  ext x 
  simp only [DistribMulAction.toLinearMap_apply, smul_assoc, LinearMap.smul_apply]

lemma ModuleAction.toLinearMap_zero {R : Type _} [CommSemiring R]
  {A : Type _} [Semiring A] [Algebra R A] {M : Type _} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] :
DistribMulAction.toLinearMap R M (0 : A) = 0 := by 
  ext x 
  simp only [DistribMulAction.toLinearMap_apply, zero_smul, LinearMap.zero_apply]

end prelim 


section actionR

open scoped TensorProduct 

variable (R : Type _) [CommSemiring R]
  (B : Type _) [Semiring B] [Algebra R B] 
variable (M N : Type _) [AddCommMonoid N] [AddCommMonoid M] [Module B N]  
  [Module R N] [IsScalarTower R B N] [Module R M] 


def tensorProductSMul_right : SMul B (M ⊗[R] N) :=
  {smul := by
    intro a 
    exact ↑(LinearMap.lTensor M (DistribMulAction.toLinearMap R N a))
  } 

def tensorProductMulAction_right : MulAction B (M ⊗[R] N) := {tensorProductSMul_right R B M N with 
  one_smul := by 
    intro x 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N 1)) _ = _ 
    rw [←DistribMulAction.toModuleEnd_apply]
    simp only [map_one]
    erw [LinearMap.lTensor_id]
    rfl
  mul_smul := by 
    intro a b x 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N (a * b))) _ = _ 
    rw [←DistribMulAction.toModuleEnd_apply]
    simp only [map_mul, DistribMulAction.toModuleEnd_apply]
    rw [LinearMap.mul_eq_comp, LinearMap.lTensor_comp]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rfl
}

def tensorProductDistribMulAction_right : DistribMulAction B (M ⊗[R] N) := {tensorProductMulAction_right R B M N with
  smul_zero := by 
    intro a 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N a)) _ = _ 
    simp only [map_zero]
  smul_add := by 
    intro a x y 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N a)) _ = _ 
    simp only [map_add]
    rfl
  }


def tensorProductModule_right : Module B (M ⊗[R] N) := {tensorProductDistribMulAction_right R B M N with
  add_smul := by
    intro a b x 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N (a + b))) _ = _
    rw [ModuleAction.toLinearMap_add, LinearMap.lTensor_add]
    simp only [LinearMap.add_apply]
    rfl
  zero_smul := by 
    intro x 
    change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N 0)) _ = _
    rw [@ModuleAction.toLinearMap_zero R _ B _ _ N _ _ _ _]
    rw [LinearMap.lTensor_zero]
    simp only [LinearMap.zero_apply]
}



def tensorProduct.IsScalarTower_right : @IsScalarTower R B (M ⊗[R] N) _ (tensorProductSMul_right R B M N) _ := by
  apply @IsScalarTower.mk R B (M ⊗[R] N) _ (tensorProductModule_right R B M N).toSMul _
  intro r a x 
  change (LinearMap.lTensor M (DistribMulAction.toLinearMap R N (r • a))) _ = _
  rw [ModuleAction.toLinearMap_smul, LinearMap.lTensor_smul]
  rw [@LinearMap.smul_apply R R R (M ⊗[R] N) (M ⊗[R] N) _ _ _ _
   TensorProduct.instModuleTensorProductToSemiringAddCommMonoid TensorProduct.instModuleTensorProductToSemiringAddCommMonoid 
   _ _ _ _ r (LinearMap.lTensor M (DistribMulAction.toLinearMap R N a)) x] 
  rfl


end actionR 

section compatibility

open scoped TensorProduct 


variable (R : Type _) [CommSemiring R]
  (A B : Type _) [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] 
variable (M N : Type _) [AddCommMonoid N] [AddCommMonoid M] [Module R M] [Module R N] [Module A M] [Module B N]  
  [IsScalarTower R A M] [IsScalarTower R B N] 


def tensorProduct.SMulCommClass : @SMulCommClass A B (M ⊗[R] N) _ (tensorProductModule_right R B M N).toSMul := by
  apply @SMulCommClass.mk A B (M ⊗[R] N) _ (tensorProductModule_right R B M N).toSMul 
  intro a b x 
  change (LinearMap.rTensor N (DistribMulAction.toLinearMap R M a)) ((LinearMap.lTensor M (DistribMulAction.toLinearMap R N b)) x) = 
     (LinearMap.lTensor M (DistribMulAction.toLinearMap R N b)) ((LinearMap.rTensor N (DistribMulAction.toLinearMap R M a)) x) 
  rw [←LinearMap.comp_apply, ←LinearMap.comp_apply]
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor] 


def tensorProduct.ModuleOverTensorProductAlgebra : Module (A ⊗[R] B) (M ⊗[R] N) := 
@TensorProduct.Algebra.module R A B (M ⊗[R] N) _ _ _ _ _ (@TensorProduct.leftModule R _ A _ M N _ _ _ _ _ _) 
(tensorProductModule_right R B M N) 
_ _ _ (tensorProduct.IsScalarTower_right R B M N)  
(tensorProduct.SMulCommClass R A B M N) 

end compatibility 

