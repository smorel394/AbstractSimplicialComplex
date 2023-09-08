import Mathlib.Tactic 
import Mathlib.LinearAlgebra.TensorProduct

open scoped TensorProduct 

variable (R : Type _) [CommSemiring R]
  (B : Type _) [Semiring B] [Algebra R B] 
variable (M N : Type _) [AddCommMonoid N] [AddCommMonoid M] [Module B N]  
  [Module R N] [IsScalarTower R B N] [Module R M] 

def module_right : Module B (M ⊗[R] N) := sorry 

def scalar_tower_right : @IsScalarTower R B (M ⊗[R] N) _ (module_right R B M N).toSMul _ := 
{smul_assoc := sorry}  -- Error: failed to synthesize instance SMul B (M ⊗[R] N)