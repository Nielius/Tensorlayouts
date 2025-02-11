import Tensorlayouts.Shape
import Tensorlayouts.HeterogenousBase

/-- ## View -/

structure View where
  shape : Shape
  stride : Stride
  lengthEq : shape.length = stride.length

deriving instance Repr for View
deriving instance DecidableEq for View

def View.mk_unchecked (shape: Shape) (stride : Stride) : Option View :=
  if h : shape.length = stride.length then
    some ⟨shape, stride, h⟩
  else
    none

def View.from_shape_unchecked (shape : Shape) : Option View :=
  View.mk_unchecked shape (Stride.from_shape shape)

def View.from_shape (shape : Shape) : View := {
  shape := shape,
  stride := Stride.from_shape shape,
  lengthEq := by
    unfold Stride.from_shape
    rw [List.scanr_length_tail]
    simp only [List.length_map]
}

theorem View.from_shape_nil : View.from_shape [] = {shape := [], stride := [], lengthEq := by simp} := by
  simp [View.from_shape, Stride.from_shape]

theorem View.from_shape_cons : View.from_shape (s :: tl) = {
  shape := s :: tl,
  stride := (tl.headD ⟨1, by simp⟩ * (Stride.from_shape tl).headD 1) :: Stride.from_shape tl,
  lengthEq := by sorry
} := by
  unfold View.from_shape
  simp [Stride.from_shape_cons]


theorem View.from_shape_shape_eq (s: Shape) : (View.from_shape s).shape = s := by
  unfold View.from_shape
  simp

theorem View.from_shape_stride_eq (s: Shape) : (View.from_shape s).stride = Stride.from_shape s := by
  unfold View.from_shape
  simp

theorem View.from_shape_stride_shape_length_eq (s: Shape) : (List.length s) = (View.from_shape s).stride.length := by
  unfold View.from_shape
  unfold Stride.from_shape
  rw [List.scanr_length_tail]
  simp only [List.length_map]


def View.from_single_dimension (shape : PosInt) (stride : Nat) : View := {
  shape := [shape],
  stride := [stride],
  lengthEq := by simp
}

theorem View.from_single_dimension_shape_eq (shape stride : PosInt) :
  (View.from_single_dimension shape stride).shape = [shape] := by
  unfold View.from_single_dimension
  simp

theorem View.from_single_dimension_stride_eq (shape : PosInt) (stride : Nat) :
  (View.from_single_dimension shape stride).stride = [stride] := by
  unfold View.from_single_dimension
  simp

theorem View.len_1_from_single_dimension (v: View) (hlen: v.shape.length = 1) :
  ∃ (shape stride : PosInt), v = View.from_single_dimension shape stride := by
  sorry

def View.nil : View := {
  shape := [],
  stride := [],
  lengthEq := by simp
}

theorem View.nil_shape_eq : (View.nil).shape = [] := by
  unfold View.nil
  simp

theorem View.nil_stride_eq : (View.nil).stride = [] := by
  unfold View.nil
  simp

def View.cons (shape: PosInt) (stride : Nat): View -> View :=
  fun v => {
    shape := shape :: v.shape,
    stride := stride :: v.stride,
    lengthEq := congrArg Nat.succ v.lengthEq
  }

theorem View.cons_shape_eq (shape stride : PosInt) (v : View) :
  (View.cons shape stride v).shape = shape :: v.shape := by
  unfold View.cons
  simp

theorem View.cons_shape_eq_cons_shape_iff {shape shape' : PosInt} {stride stride' : PosInt} {v v2 : View} :
 (cons shape stride v2).shape = (cons shape' stride' v).shape ↔ shape = shape' ∧ v2.shape = v.shape := by
  repeat rw [View.cons_shape_eq]
  apply List.cons_eq_cons

theorem View.cons_stride_eq (shape : PosInt) (stride : Nat) (v : View) :
  (View.cons shape stride v).stride = stride :: v.stride := by
  unfold View.cons
  simp


theorem View.induction (P : View → Prop)
  (nil : P View.nil)
  (cons : ∀ (x : PosInt) (xs : Shape) (y : Nat) (ys : Stride)
          (h : xs.length = ys.length)
          (ih : P ⟨xs, ys, h⟩),
          P ⟨x::xs, y::ys, congrArg Nat.succ h⟩) :
  ∀ (v : View), P v := by
  intro v
  cases v with
  | mk shape stride lengthEq =>
    -- Do induction on shape, but we need to handle stride in parallel
    revert stride
    induction shape with
    | nil =>
      -- In nil case, stride must also be nil due to length equality
      intros stride lengthEq
      have strideNil : stride = [] := by
        rw [List.length_nil] at lengthEq
        apply List.eq_nil_of_length_eq_zero
        exact Eq.symm lengthEq
      subst strideNil
      exact nil

    | cons head tail ih =>
      -- In cons case, stride must be non-empty due to length equality
      intros stride lengthEq
      cases stride with
      | nil =>
        rw [List.length] at lengthEq
        simp at lengthEq
      | cons y ys =>
        -- Use the inductive hypothesis with the tails
        have tailLenEq : tail.length = ys.length := by
          rw [List.length_cons] at lengthEq
          rw [List.length_cons] at lengthEq
          exact Nat.succ.inj lengthEq

        have ihP := ih ys tailLenEq
        exact cons head tail y ys tailLenEq ihP


/- ### Index functions -/

/--
  The smallest strict upper bound for the index that the view can represent.

  This is equal to ∑_i (s_i - 1) σ_i + 1, where σ_i is the ith stride, and s_i is the ith size.
  This assumes all strides are positive! In theory you could have negative strides...
  The ` + 1` at the end of this formula is to make it a strict upper bound,
  so that it is compatible with Shape.max_index (as proven by View.max_index_from_shape).
-/
def View.max_index (v : View) : Nat :=
  v.stride.inner_prod (v.shape.map (fun x => x - 1)) + 1


theorem View.cons_max_index :
  (View.cons shape_head stride_head v).max_index
  = (shape_head - 1) * stride_head + v.max_index := by
  unfold View.max_index
  simp [View.cons, List.inner_prod_cons, List.map_cons, List.foldr_cons]
  simp_arith
  apply Nat.mul_comm


theorem View.nil_max_index : (View.nil).max_index = 1 := by
  unfold View.max_index
  simp [View.nil]
  rfl


theorem View.max_index_is_positive : ∀ (v : View), v.max_index > 0 := by
  intro v
  unfold View.max_index
  simp [View.nil]


theorem View.max_index_from_shape (s : Shape) : (View.from_shape s).max_index = s.max_index := by
  induction s
  case nil =>
    simp [View.max_index, Shape.max_index, View.from_shape_nil]
    rfl

  case cons hd tl ih =>
    -- The only non-straightforward part is Stride.from_shape_cons_eq_max_index,
    -- and perhaps the
    simp [Shape.max_index_cons, Stride.from_shape_cons_eq_max_index]
    unfold View.max_index
    simp
    rw [← ih]
    rw [View.from_shape_stride_eq]
    rw [Stride.from_shape_cons_eq_max_index]
    rw [View.from_shape_shape_eq]
    simp

    have heq:  ((Stride.from_shape tl)).inner_prod (List.map ((fun x ↦ x - 1) ∘ Subtype.val) tl) + 1 = (from_shape tl).max_index := by
      unfold View.max_index
      rw [View.from_shape_shape_eq, View.from_shape_stride_eq, List.comp_map]

    conv =>
      lhs
      rw [List.inner_prod_cons]
      rw [Nat.add_assoc]
      rw [heq]
      rw [Nat.mul_comm]
      rw [ih]
      simp
      rw [← Nat.succ_mul]
      simp

    rw [Nat.sub_add_cancel]
    rw [ih]
    apply hd.property


theorem View.from_single_dimension_max_index_eq : ∀ (shape stride : PosInt),
  (View.from_single_dimension shape stride).max_index = (shape - 1) * stride + 1 := by
  intro shape stride
  unfold View.from_single_dimension
  unfold View.max_index
  simp [List.inner_prod]
  apply Nat.mul_comm


theorem View.from_single_dimension_max_index_le : ∀ (shape stride : PosInt),
  (View.from_single_dimension shape stride).max_index ≤ shape * stride := by
  intro shape stride
  rw [View.from_single_dimension_max_index_eq]
  rw [Nat.mul_comm]

  have hstride_pos : 1 ≤ stride.val := stride.property
  have hshape_pos : 1 ≤ shape.val := shape.property
  calc
    (stride : Nat) * (shape - 1) + 1 ≤ stride * (shape - 1) + stride := by sorry
    _ = stride * (shape - 1 + 1) := by apply Nat.mul_add_one
    _ = stride * shape := by rw [Nat.sub_add_cancel hshape_pos]

  rw [Nat.mul_comm]


-- theorem View.from_single_dimension_index_set_eq : ∀ (shape stride : PosInt),
--   (View.from_single_dimension shape stride).to_index_fn_unsafe = (fun idx => (shape - 1) * stride + idx) := by


/- ### Index functions for views -/

def View.index_fn_inner (v : View) : List Nat -> Nat :=
  v.stride.inner_prod

theorem View.index_fn_inner_additive (v : View) (l l' : List Nat) :
  v.index_fn_inner (List.zipWith (fun x y => x + y) l l') = v.index_fn_inner l + v.index_fn_inner l' := by
  sorry

def View.index_fn (v : View) : (IndexSet v.shape) -> NatLt v.max_index :=
  Subtype.map v.index_fn_inner (by
    intro idx hvalid
    unfold View.index_fn_inner
    simp
    have hasdf : forall (n : Nat), n = v.shape.length -> (v.stride.inner_prod idx < v.max_index) := by
      -- introducing this is the only way I know of doing induction on n, while keeping the right hypotheses in the goal
      intro n hn
      induction n
      . have hshape_empty: v.shape = [] := by
          apply List.eq_nil_of_length_eq_zero
          exact (Eq.symm hn)

        have hstride_empty: v.stride = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hlen : v.stride.length = 0 := by
            rw [<- v.lengthEq]
            exact (Eq.symm hn)
          assumption

        simp [hshape_empty, hstride_empty]
        simp [View.max_index, List.inner_prod, List.map, List.foldr]

      case succ n ih =>
        -- I should have made sure the induction hypothesis holds for any view, not just this v

        have hshape_cons : _ := List.exists_cons_of_length_eq_add_one (Eq.symm hn)
        obtain ⟨shape_hd, shape_tl, hshape_cons'⟩ := hshape_cons

        -- have hstride_len : _ := List.length_eq_add_one_of_cons hshape_cons'
        have hstride_cons : _ := List.exists_cons_of_length_eq_add_one (Eq.symm hn)
        obtain ⟨stride_hd, stride_tl, hstride_cons'⟩ := hstride_cons

        sorry --- it is achievable from this point

    apply (hasdf v.shape.length (Eq.refl v.shape.length))
  )

example : View :=
  View.from_shape [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨54, by simp⟩]


theorem View.from_single_dimension_index_fn_safe_eq (shape stride : PosInt) :
  (View.from_single_dimension shape stride).index_fn =
  (fun idx => ⟨ (IndexSet.from_single_dimension_equiv idx).val * stride, by sorry ⟩) := by
  funext idx

  /- Prove ⟨[(↑idx).head ⋯], ⋯⟩ = idx -/
  have := (Equiv.left_inv (@IndexSet.from_single_dimension_equiv shape)) idx
  unfold Function.LeftInverse at this
  unfold IndexSet.from_single_dimension_equiv at this
  simp at this
  rw [<- this]

  simp [View.from_single_dimension, View.index_fn]
  unfold View.index_fn_inner
  simp [View.from_single_dimension, View.index_fn]

  conv =>
    lhs
    repeat rw [Subtype.map_comp (x := idx)]
    simp
  unfold Subtype.map
  simp
  rw [List.inner_prod_singleton_left]
  rw [Nat.mul_comm]
  simp


theorem View.from_single_dimension_index_fn_safe_linear (shape stride : PosInt) (hshape : shape.val > 1) :
  NatLt.embed_nat ∘ (View.from_single_dimension shape stride).index_fn =
  ({ slope := stride, max_val := ⟨ shape.val, hshape ⟩ } : LinearIntegerFunc).fun ∘ IndexSet.from_single_dimension_equiv  := by

  rw [View.from_single_dimension_index_fn_safe_eq]
  unfold LinearIntegerFunc.fun
  simp
  funext idx
  simp
  rw [Nat.mul_comm]


theorem View.index_fn_is_linear (v: View) (i : IndexFnSet v.shape) (j : Fin v.shape.length) (h : i.val j + 1 < v.shape.get j) :
    (v.index_fn (IndexSet.fn_equiv.symm (incrementIndex i j h))).val
  - (v.index_fn (IndexSet.fn_equiv.symm i)).val
  = (v.index_fn (IndexSet.fn_equiv.symm (incrementIndex (IndexSet.zero v.shape).fn_equiv j (by sorry)))).val := by
  /- BELANGRIJK GEBLEVEN : deze twee lemmas zijn belangrijk om nog op te lossen -/
  sorry


theorem View.index_fn_step_is_stride (v: View) (i : IndexFnSet v.shape) (j : Fin v.shape.length) (h : i.val j + 1 < v.shape.get j) :
    (v.index_fn (IndexSet.fn_equiv.symm (incrementIndex i j h))).val =
    (v.index_fn (IndexSet.fn_equiv.symm i)).val + v.stride.get ⟨↑j, (by
      rw [<- v.lengthEq]
      exact j.isLt
    )⟩ := by
  sorry


/- ### Views from linear functions -/

def View.from_linear_function (f : LinearIntegerFunc) : View :=
  View.from_single_dimension ⟨f.max_val, by sorry ⟩ f.slope

theorem View_from_linear_function_to_linear_function (f : LinearIntegerFunc) :
  NatLt.embed_nat ∘ (View.from_linear_function f).index_fn = f.fun ∘ IndexSet.from_single_dimension_equiv := by
  sorry

theorem View.from_linear_function_shape_eq (f : LinearIntegerFunc) :
  (View.from_linear_function f).shape = [⟨f.max_val, by sorry ⟩] := by
  unfold View.from_linear_function
  unfold View.from_single_dimension
  simp







/-- ## Unraveling -/

def unravel_inner (s : Shape) : Nat -> List Nat :=
  fun idx =>
    List.zipWith (fun shape stride => (idx / stride) % shape) s (Stride.from_shape s)


def unravel (s : Shape) : NatLt s.max_index -> IndexSet s :=
  Subtype.map (unravel_inner s) (by
      intro idx hvalid
      unfold unravel_inner
      unfold Shape.is_valid_index
      simp

      have hlen : List.length s ≤ List.length (Stride.from_shape s) := by rw [Stride.from_shape_length]
      exists hlen

      have hminlen : s.length ⊓ (Stride.from_shape s).length = List.length s := by
        simp only [inf_eq_left, Stride.from_shape_length, le_refl]

      intros i hbound
      rw [<- Nat.lt_min] at hbound
      rewrite [hminlen] at hbound
      apply Nat.mod_lt
      exact (s.get ⟨i, hbound⟩).property
  )

/--
Interpretation: the input is a Nat representing an entry in the tensor; the output is the memory index
-/
def View.to_unraveled_index_fn (v : View) : NatLt v.shape.max_index -> NatLt v.max_index :=
  v.index_fn ∘ unravel v.shape

/--
unravel is the inverse of the index function for the default view for a shape

We could make this a bit more general: if we extend unravel to all of Nat,
then this is also true for any n : Nat.
-/
theorem unravel_correct {s : Shape} (n : NatLt s.max_index) :
  (View.from_shape s).to_unraveled_index_fn n = (n : Nat) % s.max_index := by
  have hbnf : (View.from_shape s).to_unraveled_index_fn n = HeterogenousBase.heterogenous_base_bnf s n := by
    unfold View.to_unraveled_index_fn
    unfold unravel
    unfold unravel_inner
    unfold View.index_fn
    unfold View.index_fn_inner
    unfold View.from_shape
    unfold HeterogenousBase.heterogenous_base_bnf
    simp
  rw [hbnf]

  exact HeterogenousBase.heterogenous_base s n


theorem unravel_correct_fn (s: Shape):
  exists
    (htype_input : NatLt (View.from_shape s).shape.max_index = NatLt s.max_index)
    (htype_output : NatLt (View.from_shape s).max_index = NatLt s.max_index) ,
     (cast htype_output) ∘ (View.from_shape s).to_unraveled_index_fn ∘ (cast htype_input) = id := by
  have htype_input : NatLt (View.from_shape s).shape.max_index = NatLt s.max_index := by
    rw [View.from_shape_shape_eq]
  have htype_output : NatLt (View.from_shape s).max_index = NatLt s.max_index := by
    rw [View.max_index_from_shape]

  exists htype_input, htype_output

  funext n
  unfold id
  unfold Function.comp
  simp

  apply Subtype.ext

  have hcast (n : NatLt (View.from_shape s).max_index): ↑ (cast htype_output n) = (n : Nat) := by
    congr
    . rw [View.max_index_from_shape]
    . simp

  rw [hcast]
  rw [unravel_correct]

  apply Nat.mod_eq_of_lt

  conv =>
    rhs
    rw [<- View.from_shape_shape_eq s]
  exact n.property

theorem unravel_correct_fn' (s: Shape):
  let (hsame_type : (View.from_shape s).shape.max_index = (View.from_shape s).max_index) := by
    rw [View.max_index_from_shape]
    rw [View.from_shape_shape_eq]
  (View.from_shape s).to_unraveled_index_fn = (Subtype.map id (fun x h => hsame_type ▸ h): NatLt (View.from_shape s).shape.max_index → NatLt (View.from_shape s).max_index) := by
  -- (fun x => ⟨ x.val, hsame_type ▸ x.prop⟩ : NatLt (View.from_shape s).shape.max_index → NatLt (View.from_shape s).max_index) := by
  -- (cast (congrArg NatLt hsame_type)) := by
  simp
  funext n
  apply Subtype.ext
  have hshape_eq  := View.from_shape_shape_eq s
  have := unravel_correct n

  /- Again, super annoying dependent rewrite that Lean doesn't find itself... -/
  have h_cast : ((View.from_shape (View.from_shape s).shape).to_unraveled_index_fn n)
              = ((View.from_shape s).to_unraveled_index_fn n) := by
    -- Use the hypothesis `hshape_eq` to simplify the left-hand side of the equation
    have := @Eq.rec _ _
      (motive := fun x (h : s = x) ↦
         (View.from_shape x).to_unraveled_index_fn (h ▸ n) = h ▸ (View.from_shape s).to_unraveled_index_fn n)
      (by rfl)
      (View.from_shape s).shape hshape_eq.symm
    simp at this
    assumption

  rw [<- h_cast]
  rw [this]

  have : ↑n % (View.from_shape s).shape.max_index = (n : Nat) := Nat.mod_eq_of_lt n.property
  rw [this]
  simp


theorem unravel_correct' (s : Shape) :
  (View.from_shape s).to_unraveled_index_fn = (fun x => ⟨ x % s.max_index, by
    rw [View.max_index_from_shape]
    apply Nat.mod_lt
    exact s.max_index_posint.property
   ⟩ ) := by
  funext n
  apply Subtype.ext
  apply unravel_correct


def View.example : View := {
  shape := [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩],
  stride := [12, 4, 1],
  lengthEq := by simp
}
