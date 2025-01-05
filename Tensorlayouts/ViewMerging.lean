import Tensorlayouts.Shape

import Mathlib.Data.Set.Basic

/--
  Expresses whether v is a merge of v1 and v2
-/
def View.is_merge (v: View) (v1 : View) (v2 : View) : Prop :=
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ v.to_index_fn_safe
  = NatLt.embed_nat ∘ v1.to_unraveled_index_fn ∘ NatLt.embedding hmaxsize ∘ (cast hshape_fn v2.to_index_fn_safe)


def View.is_mergeable  (v1 : View) (v2 : View) : Prop :=
  ∃(v: View), v.is_merge v1 v2



theorem simple_example (k k' : Nat) (n : NatLt k) (h : NatLt k = NatLt k'):
  (cast h n) = (n : Nat) := by
  rw [<- Subtype.heq_iff_coe_eq]
  unfold cast
  rw [eqRec_heq_iff_heq]


  intro x

  let t := Set.coe_setOf (fun x => x < k)
  let t' := Set.coe_setOf (fun x => x < k')

  unfold NatLt at h
  rw [h] at t
  rw [<- t'] at t




  constructor
  . intro xt
    let xprop := (⟨ x, xt ⟩ : NatLt k')
    let xprop_cast := cast (Eq.symm h) xprop

    have asset :=  { x | x < k }
    have asset' :=  { x | x < k' }


    let t := Set.coe_setOf (fun x => x < k)
    let t' := Set.coe_setOf (fun x => x < k')

    unfold NatLt at h
    rw [h] at t
    rw [<- t'] at t






    have hteq :  ↥ asset  = ↥ asset' := by
      rw [t]





      congr

    have asdf :  asset  = NatLt k := by


    asset


    exact xprop_cast.property











  apply Subtype.eq_iff


  congr 1
  .

  . simp

  rw [<- heq_iff_eq]

  simp




  simp
  rw [h]
  simp [h]
  congr

  NatLt.embed_nat ∘ cast (by simp) ∘ NatLt.embedding (by simp) ∘ (by simp) = NatLt.embed_nat := by
  simp


theorem View.is_mergeable_left_canonical (s : Shape) (v2 : View) (hmaxsize : v2.max_index ≤ s.max_index) :
  View.is_mergeable (View.from_shape s) v2 := by
  exists v2
  unfold View.is_merge

  have hshape : v2.shape = v2.shape := by rfl
  exists hshape

  exists hmaxsize

  cases (unravel_correct_fn' s) with
  | intro hshape_fn hcorrect_fn =>
    simp
    rw [hcorrect_fn]

    have hembed : NatLt.embed_nat ∘ cast hshape_fn ∘ NatLt.embedding hmaxsize = NatLt.embed_nat := by
      funext n'
      simp [NatLt.embedding, NatLt.embed_nat]
      unfold Subtype.val
      norm_cast
      simp_all only



      simp



      #check @Eq.rec
      @Eq.rec Type (NatLt (from_shape s).shape.max_index) (fun x x_1 ↦ x) ⟨n'.1, ⋯⟩ (NatLt (from_shape s).max_index) hshape_fn : NatLt (from_shape s).max_index




      congr
      . sorry
      . have hc : _ := cast_heq hshape_fn n




      rw [<- eq_mp_eq_cast]




      congr
      . sorry
      .













  simp
  rw [unravel_correct' s]









  rw [unravel_correct' s]



  swap
  . simp
  .
    simp [View.from_shape]
    unfold View.to_index_fn_safe
    unfold View.to_unraveled_index_fn
    simp
    funext x
    unfold unravel
    unfold unravel_unsafe
    simp








  case w






  unfold View.is_merge



  un


example : View.is_mergeable (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) := by
  exists (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩]))
