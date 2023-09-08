import Mathlib.Tactic 
import Mathlib.Init.Order.Defs
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Sum.Order
import Mathlib.Order.WellFounded
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Data.Set.Image
import Mathlib.Order.PFilter
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Real.Basic


set_option autoImplicit false


open Classical 

universe u 

variable {α : Type u}


/- Some lemmas for total preorders. -/

/- If ≤ is a total preorder on α, then for all a,b in α, we have a < b, b < a or (a ≤ b and b ≤ a).-/
lemma TotalPreorder_trichotomy {s : Preorder α} (htot : Total s.le) (a b : α) :
s.lt a b ∨ s.lt b a ∨ AntisymmRel s.le a b := by
  by_cases hltab : s.lt a b
  . exact Or.inl hltab
  . by_cases hltba : s.lt b a 
    . exact Or.inr (Or.inl hltba)
    . rw [s.lt_iff_le_not_le] at hltab hltba
      push_neg at hltab hltba
      cases (htot a b) with
      | inl hab => exact Or.inr (Or.inr ⟨hab, hltab hab⟩)
      | inr hba => exact Or.inr (Or.inr ⟨hltba hba, hba⟩)

/- Trichotomy for a linear order, given as a preorder satisfying IsLinearOrder.-/
lemma LinearPreorder_trichotomy {s : Preorder α} (hlin : IsLinearOrder α s.le) (a b : α) :
s.lt a b ∨ s.lt b a ∨ a=b := by
  have halmost := TotalPreorder_trichotomy hlin.toIsTotal.total a b
  rw [@antisymmRel_iff_eq α s.le {refl := s.le_refl} hlin.toIsPartialOrder.toIsAntisymm a b] at halmost 
  exact halmost 

/- If ≤ is a total preorder on α and a,b are elements of α, then ¬(a ≤ b) is equivalent to b < a.-/
lemma TotalPreorder_lt_iff_not_le {s : Preorder α} (htot : Total s.le) {a b : α} : ¬(s.le a b) ↔ s.lt b a := by
  rw [s.lt_iff_le_not_le]
  simp only [iff_and_self]
  intro hnab
  cases (htot a b) with
  | inl hab => exfalso; exact hnab hab  
  | inr hba => exact hba 



/- A preorder is called Noetherian if it has no infinite ascending chain.-/
def IsNoetherianPoset (α : Type u) [s : Preorder α] : Prop := WellFounded (fun a b => s.lt b a)
 

/- We introduce "maximal nonproper" order ideals, i.e. order ideals that are maximal among all
order ideals (not just the proper ones). This is only interesting when α is not known to be directed,
so ⊤ might not be an order ideal.-/

section

variable [Preorder α]


@[mk_iff]
class Order.Ideal.IsMaximalNonProper (I : Order.Ideal α) : Prop where
maximal_nonproper : ∀ ⦃J : Order.Ideal α⦄, I ≤ J → I = J 


/- Every order ideal is contained in a maximal nonproper order ideal. -/

/- Order ideals form an inductive set (every chain has an upper bound).-/
lemma OrderIdeals_inductive_set : ∀ (c : Set (Order.Ideal α)), IsChain (fun I J => I ≤ J) c → ∀ (I : Order.Ideal α), 
I ∈ c → ∃ (ub : Order.Ideal α), ∀ (J : Order.Ideal α), J ∈ c → J ≤ ub := by 
  intro c hchain I hIc 
  set J := ⋃ (K : c), (K.1.carrier : Set α)  
  have hJdef : ∀ (K : Order.Ideal α), K ∈ c → (K : Set α) ⊆ J := by 
    intro K hKc 
    exact Set.subset_iUnion (fun (K : c) => (K : Set α)) ⟨K, hKc⟩   
  have hJne : J.Nonempty := by cases I.nonempty' with
                               | intro a haI => exists a; exact (hJdef I hIc) haI 
  have hJls : IsLowerSet J := by 
    intro s t hts hsJ 
    rw [Set.mem_iUnion] at hsJ ⊢
    cases hsJ with 
    | intro K hK => exists K; exact K.1.toLowerSet.lower' hts hK 
  have hJdo : DirectedOn (fun s t => s ≤ t) J := by 
    intro s hsJ t htJ 
    rw [Set.mem_iUnion] at hsJ htJ 
    cases hsJ with 
    | intro K hsK => cases htJ with
                    | intro L htL => cases IsChain.total hchain K.2 L.2 with 
                                     | inl hKL => have hsL : s ∈ (L : Set α) := hKL hsK 
                                                  cases L.1.directed' s hsL t htL with 
                                                  | intro u hu => exists u 
                                                                  constructor
                                                                  . rw [Set.mem_iUnion]
                                                                    exists L 
                                                                    exact hu.1
                                                                  . exact hu.2    
                                     | inr hLK => have htK : t ∈ (K : Set α) := hLK htL 
                                                  cases K.1.directed' s hsK t htK with 
                                                  | intro u hu => exists u 
                                                                  constructor
                                                                  . rw [Set.mem_iUnion]
                                                                    exists K 
                                                                    exact hu.1
                                                                  . exact hu.2    
  exists Order.IsIdeal.toIdeal {IsLowerSet := hJls, Nonempty := hJne, Directed := hJdo}
  

/- Every order ideal is contained in a maximal nonproper order ideal.-/
lemma Order.Ideal.contained_in_maximal_nonproper (I : Order.Ideal α): ∃ (J : Order.Ideal α), Order.Ideal.IsMaximalNonProper J ∧ I ≤ J := by 
  cases @zorn_nonempty_partialOrder₀ (Order.Ideal α) _ Set.univ 
    (fun c _ hchain J hJc => by cases @OrderIdeals_inductive_set α _ c hchain J hJc with 
                                | intro ub hub => exists ub) I (Set.mem_univ _)  with 
  | intro J hJ => exists J  
                  erw [and_iff_left hJ.2.1, Order.Ideal.IsMaximalNonProper_iff]
                  exact fun K hJK => Eq.symm (hJ.2.2 K (Set.mem_univ _) hJK) 

/- If an order ideal has a maximal element, then this element generates the ideal.-/
lemma Order.Ideal.generated_by_maximal_element (I : Order.Ideal α) {a : α} (ha : a ∈ I ∧ ∀ (b : α), b ∈ I → a ≤ b → b ≤ a) : 
I = Order.Ideal.principal a := by 
  rw [←Order.Ideal.principal_le_iff] at ha
  refine le_antisymm ?_ ha.1 
  intro b hbI 
  erw [Order.Ideal.mem_principal] 
  cases I.directed a (by rw [Order.Ideal.principal_le_iff] at ha; exact ha.1) b hbI with
  | intro c hc => exact le_trans hc.2.2 (ha.2 c hc.1 hc.2.1)

/- If an order filter has a minimal element, then this element generates the filter.-/
lemma Order.PFilter.generated_by_minimal_element (F : Order.PFilter α) {a : α} (ha : a ∈ F ∧ ∀ (b : α), b ∈ F → b ≤ a → a ≤ b) : 
F = Order.PFilter.principal a := by 
  suffices hdual : F.dual = @Order.Ideal.principal αᵒᵈ _ a by  
    unfold Order.PFilter.principal 
    erw [←hdual]
  apply Order.Ideal.generated_by_maximal_element F.dual
  change a ∈ F.dual ∧ _ at ha
  rw [and_iff_right ha.1]
  exact fun b hbF hab => ha.2 b hbF hab   



/- The preodered set α is Noetherian if and only if every order ideal of α is principal.-/
lemma Noetherian_iff_every_ideal_is_principal_aux (hprin : ∀ (I : Order.Ideal α), ∃ (a : α), I = Order.Ideal.principal a) (s : Set α) 
(c : Set α) (hcs : c ⊆ s) (hchain : IsChain (fun a b => a ≤ b) c) (a : α) (hac : a ∈ c) : 
∃ (m : α), m ∈ s ∧ ∀ (b : α), b ∈ c → b ≤ m := by 
  set J := ⋃ (a : c), ((Order.Ideal.principal a.1).carrier : Set α) with hJdef
  have hJdef : ∀ (a : α), a ∈ c → ((Order.Ideal.principal a).toLowerSet.carrier : Set α) ⊆ J := by 
    intro a hac 
    rw [hJdef]
    refine Set.subset_iUnion (fun (a : c) => ((Order.Ideal.principal a.1).toLowerSet.carrier : Set α)) ⟨a, hac⟩    
  have hJne : J.Nonempty := by exists a
                               refine (hJdef a hac) ?_  
                               erw [Order.Ideal.mem_principal]
  have hJls : IsLowerSet J := by 
    intro b d hdb hbJ 
    rw [Set.mem_iUnion] at hbJ ⊢
    cases hbJ with 
    | intro e he => exists e; erw [Order.Ideal.mem_principal] at he ⊢; exact le_trans hdb he  
  have hJdo : DirectedOn (fun b d => b ≤ d) J := by 
    intro b hbJ d hdJ 
    rw [Set.mem_iUnion] at hbJ hdJ 
    cases hbJ with 
    | intro e he => cases hdJ with
                    | intro f hd => cases IsChain.total hchain e.2 f.2 with 
                                    | inl hef => exists f
                                                 have hfJ := hJdef f.1 f.2
                                                 rw [and_iff_right (hfJ (by have hff := le_refl ↑f; rw [←Order.Ideal.mem_principal] at hff; exact hff))]
                                                 erw [Order.Ideal.mem_principal] at hd he
                                                 exact ⟨le_trans he hef, hd⟩
                                    | inr hfe => exists e
                                                 have heJ := hJdef e.1 e.2
                                                 rw [and_iff_right (heJ (by have hee := le_refl ↑e; rw [←Order.Ideal.mem_principal] at hee; exact hee))]
                                                 erw [Order.Ideal.mem_principal] at hd he
                                                 exact ⟨he, le_trans hd hfe⟩
  cases hprin (Order.IsIdeal.toIdeal {IsLowerSet := hJls, Nonempty := hJne, Directed := hJdo}) with
  | intro b hb => apply_fun (fun I => I.carrier) at hb 
                  change J = _ at hb 
                  have hbmax : ∀ (d : α), d ∈ c → d ≤ b := by 
                    intro d hdc 
                    have hdJ : d ∈ J := by rw [Set.mem_iUnion]
                                           exists ⟨d,hdc⟩
                                           erw [Order.Ideal.mem_principal]
                    erw [hb, Order.Ideal.mem_principal] at hdJ
                    exact hdJ
                  have hbJ : b ∈ J := by erw [hb, Order.Ideal.mem_principal] 
                  rw [Set.mem_iUnion] at hbJ
                  cases hbJ with 
                  | intro d hbd => erw [Order.Ideal.mem_principal] at hbd 
                                   exists d 
                                   rw [and_iff_right (hcs d.2)]
                                   intro e hec 
                                   exact le_trans (hbmax e hec) hbd  


lemma Noetherian_iff_every_ideal_is_principal : IsNoetherianPoset α  ↔ ∀ (I : Order.Ideal α), ∃ (a : α), I = Order.Ideal.principal a := by
  constructor
  . intro hNoeth I 
    exists WellFounded.min hNoeth I I.nonempty
    apply Order.Ideal.generated_by_maximal_element 
    erw [and_iff_right (WellFounded.min_mem hNoeth I I.nonempty)] 
    intro b hbI hab 
    have hnlt := WellFounded.not_lt_min hNoeth I I.nonempty hbI
    rw [lt_iff_le_not_le] at hnlt
    push_neg at hnlt 
    exact hnlt hab    
  . intro hprin
    unfold IsNoetherianPoset
    rw [WellFounded.wellFounded_iff_has_min]
    intro s hsne 
    cases hsne with
    | intro a has => cases zorn_nonempty_preorder₀ s 
                       (fun c hcs hchain b hbc => @Noetherian_iff_every_ideal_is_principal_aux α _ hprin s c hcs hchain b hbc) 
                       a has with  
                     | intro m hm => exists m 
                                     rw [and_iff_right hm.1]
                                     exact fun b hbs => by rw [lt_iff_le_not_le]; push_neg; exact hm.2.2 b hbs



end 


/- For a partial order, the order embedding from α to order ideals of α (sending an element to the principal ideal it generates). -/
section 
variable [PartialOrder α]

def Elements_to_Ideal : OrderEmbedding α (Order.Ideal α) where 
toFun := fun a => Order.Ideal.principal a 
inj' := by intro a b heq; simp only at heq
           refine le_antisymm ?_ ?_ 
           rw [←Order.Ideal.mem_principal, ←heq, Order.Ideal.mem_principal]
           rw [←Order.Ideal.mem_principal, heq, Order.Ideal.mem_principal]
map_rel_iff' := by intro a b
                   simp only [Function.Embedding.coeFn_mk, Order.Ideal.principal_le_iff, Order.Ideal.mem_principal]

end 


/- Locally finite and locally finite with bot instance on Finset α.-/

/- First we prove that left-infinite right-closed intervals are finite.-/
lemma FinsetIic_is_finite (s : Finset α) : (Set.Iic s).Finite := by
  rw [←Set.finite_coe_iff]
  apply Finite.of_injective (fun (t : Set.Iic s) => ({a : s | a.1 ∈ t.1} : Set s))
  intro t u htu
  simp only at htu 
  rw [←SetCoe.ext_iff]
  ext a 
  constructor 
  . exact fun ha => by have has : a ∈ s := t.2 ha 
                       set a' := (⟨a, has⟩ : {a : α | a ∈ s})
                       have hat : a' ∈ {a : s| a.1 ∈ t.1} := by simp only [Finset.setOf_mem, Finset.coe_sort_coe, Set.mem_setOf_eq]; exact ha
                       rw [htu] at hat 
                       exact hat 
  . exact fun ha => by have has : a ∈ s := u.2 ha
                       set a' := (⟨a,has⟩ : {a : α | a ∈ s})
                       have hau : a' ∈ {a : s| a.1 ∈ u.1} := by simp only [Finset.setOf_mem, Finset.coe_sort_coe, Set.mem_setOf_eq]; exact ha
                       rw [←htu] at hau 
                       exact hau 

/-Then that closed intervals are finite.-/
lemma FinsetIcc_is_finite (s t : Finset α) : (Set.Icc s t).Finite := 
Set.Finite.subset (FinsetIic_is_finite t) (by rw [Set.subset_def]; simp only [ge_iff_le, gt_iff_lt, Set.mem_Icc, Set.mem_Iic, and_imp, imp_self, 
implies_true, Subtype.forall, forall_const])

/- LocallyFiniteOrderBot instance on Finset α.-/
noncomputable instance FinsetLFB : LocallyFiniteOrderBot (Finset α) :=
LocallyFiniteOrderTop.ofIic (Finset α) (fun s => Set.Finite.toFinset (FinsetIic_is_finite s)) 
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic]) 

/- LocallyFiniteOrder instance on Finset α.-/
noncomputable instance FacePosetLF : LocallyFiniteOrder (Finset α) :=
LocallyFiniteOrder.ofIcc (Finset α) (fun s t => Set.Finite.toFinset (FinsetIcc_is_finite s t)) 
  (fun a s t => by simp only [ge_iff_le, gt_iff_lt, Set.Finite.mem_toFinset, Set.mem_Icc]) 

