import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp
import Mathlib.Algebra.Group.Defs -- for AddMonoid
import Mathlib.Data.Finset.Basic -- for Finset.range
import Mathlib.Data.Fintype.BigOperators -- for ∑
import Mathlib.Algebra.BigOperators.Fin -- for Fin.sum_univ_succ


def Nat.prod (l : List Nat) : Nat :=
  List.foldr (fun x acc => x * acc) 1 l

theorem Nat.prod_nil : Nat.prod [] = 1 := by
  unfold Nat.prod
  rw [List.foldr_nil]

theorem Nat.prod_cons : Nat.prod (a :: l) = a * Nat.prod l := by
  unfold Nat.prod
  rw [List.foldr_cons]

def List.zeros (len : Nat) : List Nat :=
  List.replicate len 0

@[simp]
def List.zeros_length {len : Nat} : (List.zeros len).length = len := by
  simp [List.zeros]

/- ## List.incrementNth -/

def List.incrementNth (xs : List Nat) (idx : Nat) : List Nat :=
  xs.modify (fun x => x + 1) idx

@[simp]
theorem List.incrementNth_length {xs : List Nat} (idx : Nat) :
  (xs.incrementNth idx).length = xs.length :=
  by
    unfold List.incrementNth
    apply List.length_modify

theorem List.incrementNth_cons {x : Nat} {xs : List Nat} (idx : Nat) :
  (x :: xs).incrementNth (idx + 1) = x :: xs.incrementNth idx := by
    unfold List.incrementNth
    unfold modify
    simp

theorem List.incrementNth_ite (xs : List Nat) (idx : Nat) (j : Fin xs.length) :
  (xs.incrementNth idx)[j] = if j.val = idx then xs[j] + 1 else xs[j] := by
  induction xs generalizing idx
  case nil =>
    apply Fin.elim0 j
  case cons x xs ih =>
    unfold List.incrementNth
    unfold modify
    simp
    cases idx
    case zero =>
      simp
      by_cases h : j.val = 0
      . simp [h]
        have : j = ⟨ 0, by simp ⟩ := by rw [<- Fin.val_eq_val]; assumption
        rw [this]
        simp
      . simp [h]
        have : j ≠ ⟨ 0, by simp ⟩ := by unfold Ne; rw [<- Fin.val_eq_val]; exact h
        obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero this
        rw [<- hj']
        simp
    case succ idx' =>
      simp
      by_cases h : j.val = 0
      . simp [h]
        have : j = ⟨ 0, by simp ⟩ := by rw [<- Fin.val_eq_val]; assumption
        rw [this]
        simp
      . have : j ≠ ⟨ 0, by simp ⟩ := by unfold Ne; rw [<- Fin.val_eq_val]; exact h
        obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero this
        rw [<- hj']
        simp
        exact ih idx' j'

def List.one_hot (len : Nat) (j : Fin len) : List Nat :=
  List.incrementNth (List.zeros len) j

@[simp]
theorem List.one_hot_length {len : Nat} (j : Fin len) :
  (List.one_hot len j).length = len := by
  simp [List.one_hot]

theorem List.one_hot_eq_iff_len_eq (len len' : Nat) (j : Fin len) (j' : Fin len') :
  List.one_hot len j = List.one_hot len' j' <->
  (len = len' ∧ j.val = j'.val) := by
  sorry
  -- constructor
  -- . intro h
  --   simp at h
  --   rw [List.one_hot_val]
  --   rw [List.one_hot_val]
  --   simp at h

  -- List.incrementNth (List.zeros len) j


/- ## List.inner_prod -/

def List.inner_prod {α: Type} [Mul α] [Add α] [Zero α] (l : List α) (r : List α) : α :=
   List.sum (List.zipWith (fun x y => x * y) l r)

theorem List.inner_prod_nil_nil {α: Type} [Mul α] [Add α] [Zero α] :
   List.inner_prod [] [] = 0 := by
  simp [List.inner_prod, List.sum_nil, List.zipWith_nil_right]

theorem List.inner_prod_nil {α: Type} [Mul α] [Add α] [Zero α] {r : List α} :
   List.inner_prod [] r = 0 := by
  simp [List.inner_prod, List.sum_nil, List.zipWith_nil_right]

theorem List.inner_prod_cons {α: Type} [Mul α] [Add α] [Zero α] (a : α) (l : List α) (b : α) (r : List α) :
   List.inner_prod (a :: l) (b :: r) = a * b + List.inner_prod l r := by
  unfold List.inner_prod
  rw [List.zipWith_cons_cons]
  rw [List.sum_cons]

theorem List.inner_prod_singleton_left {α: Type} [Mul α] [Add α] [Zero α] (a : α) (b : α) (r : List α) :
   List.inner_prod [a] (b :: r) = a * b + 0 := by
   simp [List.inner_prod, List.zipWith]

theorem List.inner_prod_cons_as_inner_prods {α: Type} [Mul α] [AddMonoid α] (a : α) (l : List α) (b : α) (r : List α) :
   List.inner_prod (a :: l) (b :: r) = List.inner_prod [a] [b] + List.inner_prod l r := by
  unfold List.inner_prod
  rw [List.zipWith_cons_cons]
  rw [List.sum_cons]
  conv =>
    rhs
    enter [1]
    unfold List.zipWith
    simp

theorem List.inner_prod_indexed {α: Type} [Mul α] [AddCommMonoid α]
   (l : List α) (r : List α)
   (h_len : l.length = r.length) :
   l.inner_prod r = ∑ i : Fin l.length, l[i] * r[i] :=
   by
   -- revert r
   induction l generalizing r
   case nil =>
    simp [List.inner_prod_nil]
   case cons hd tl ih =>
    cases r with
    | nil =>
      contradiction
    | cons hd' tl' =>
      rw [List.inner_prod_cons]
      simp
      rw [Fin.sum_univ_succ]
      simp
      have := ih tl' (by
        rw [List.length_cons] at h_len
        rw [List.length_cons] at h_len
        rw [Nat.add_one_inj] at h_len
        exact h_len
      )
      rw [this]
      simp


theorem List.inner_prod_zeros_left {len : Nat} :
  ∀ (r : List Nat), List.inner_prod (List.zeros len) r = 0 := by
  induction len
  . intro r
    simp [List.zeros]
    unfold List.inner_prod
    simp only [zipWith_nil_left, sum_nil]
  case succ len ih =>
    simp [List.zeros]
    rw [List.replicate_succ]
    intro r
    cases r
    case nil =>
      unfold List.inner_prod
      simp
    case cons hd tl =>
      rw [List.inner_prod_cons]
      have := ih tl
      simp [List.zeros] at this
      rw [this]
      simp

theorem List.inner_prod_symmetric {l : List Nat} {r : List Nat} (h_len : l.length = r.length) :
  List.inner_prod l r = List.inner_prod r l := by
  rw [List.inner_prod_indexed l r h_len]
  rw [List.inner_prod_indexed r l (by sorry)]
  simp
  conv =>
    lhs
    pattern fun _ => _ * _
    intro i
    rw [Nat.mul_comm]

  -- EXAMPLE: of how I just can't use l.length = r.length, and need to manually write an Eq.rec...
  have := @Eq.rec _ _
      (motive := fun ll (h : l.length = ll) ↦ ((@Finset.sum (Fin l.length) ℕ Nat.instAddCommMonoid Finset.univ fun i ↦ r[i.val] * l[i.val] : ℕ)
                                              = (@Finset.sum (Fin ll) ℕ Nat.instAddCommMonoid Finset.univ fun i ↦ r[i.val] * l[i.val] : ℕ)))
      (by
        simp
      ) r.length h_len
  rw [this]


lemma List_inner_prod_increment_left_head {x : Nat} {xs : List Nat} {y : Nat} {ys : List Nat} :
  ((x + 1) :: xs).inner_prod (y :: ys) = (x :: xs).inner_prod (y :: ys) + y := by
  repeat rw [List.inner_prod_cons]
  rw [Nat.add_mul]
  omega


theorem List.inner_prod_increment_left {xs : List Nat} {ys : List Nat} (h_len : xs.length = ys.length) :
  ∀ (idx : Nat) (h_idx : idx < xs.length), List.inner_prod (xs.incrementNth idx) ys = List.inner_prod xs ys + ys[idx] := by
  induction xs generalizing ys
  case nil =>
    intros idx h_idx
    -- Since xs is empty, xs.length = 0, so there is no element of type Fin xs.length.
    simp at h_idx
  case cons x xs ih =>
    intros idx h_idx
    cases ys with
    | nil =>
      simp at h_len
    | cons y ys' =>
      -- Since (x :: xs).length = (y :: ys').length, we have xs.length = ys'.length.
      have h_len' : xs.length = ys'.length := by exact Nat.succ_inj'.mp h_len
      -- Now do a case analysis on idx.

      cases idx with
      | zero =>
        simp
        unfold List.incrementNth
        unfold modify
        simp
        rw [List_inner_prod_increment_left_head]
      | succ k' =>
        simp
        rw [List.incrementNth_cons]
        rw [List.inner_prod_cons]
        let k'fin : Fin (xs.length) := ⟨k', by simp at h_idx; exact h_idx ⟩
        have : k' = k'fin.val := by unfold k'fin; simp
        conv =>
          lhs
          rw [this]
        rw [@ih]
        conv =>
          rhs
          rw [List.inner_prod_cons]
        rw [Nat.add_assoc]
        assumption
        exact k'fin.is_lt


theorem List.inner_prod_one_hot (xs : List Nat) (j : Fin xs.length) :
  List.inner_prod (List.one_hot xs.length j) xs = xs[j] := by
  unfold List.one_hot
  rw [List.inner_prod_increment_left]
  simp
  apply List.inner_prod_zeros_left
  simp
  simp


/-- ## PosInt -/

def PosInt := { n : Nat // n > 0 }
-- problem with this approach:
-- many things that work with Nat (e.g. omega)
-- don't seem to work automatically with PosInt; e.g. commutativity of multiplication

deriving instance Repr for PosInt
deriving instance DecidableEq for PosInt

instance : Coe PosInt Nat :=
  ⟨Subtype.val⟩

instance : Add PosInt where
  add a b := ⟨a + b, by refine Nat.add_pos_left a.property b.val⟩

instance : HMul PosInt PosInt PosInt where
  hMul a b := ⟨a * b, Nat.mul_pos a.property b.property⟩

instance : Mul PosInt where
  mul a b := ⟨a * b, Nat.mul_pos a.property b.property⟩

theorem PosInt.mul_comm (a b : PosInt) : a * b = b * a := by
   unfold HMul.hMul
   unfold instHMulPosInt
   simp
   have h : a.val * b.val = b.val * a.val := by
      exact Nat.mul_comm a.val b.val
   simp [h]
instance : Std.Commutative (α := PosInt) (· * ·) := ⟨PosInt.mul_comm⟩

-- Order instances
instance : LT PosInt := ⟨λ a b => a.val < b.val⟩
instance : LE PosInt := ⟨λ a b => a.val ≤ b.val⟩
instance : DecidableRel (· < · : PosInt → PosInt → Prop) := inferInstance
instance : DecidableRel (· ≤ · : PosInt → PosInt → Prop) := inferInstance

instance : ToString PosInt where
  toString a := toString a.val


/-- ## NatLT -/

abbrev NatLt (n : Nat) : Type := { idx : Nat // idx < n }

@[simp]
def NatLt.embedding {n m : Nat} (h : n ≤ m) : NatLt n -> NatLt m :=
  Subtype.map id (fun _ xprop => Nat.lt_of_lt_of_le xprop h)

def NatLt.embed_nat {n : Nat} : NatLt n -> Nat :=
  fun x => x.val

theorem NatLt.embedding_comp {n m k : Nat} (h1 : k ≤ n) (h2 : m ≤ k) : NatLt.embedding h1 ∘ NatLt.embedding h2 = NatLt.embedding (Nat.le_trans h2 h1) := by
  funext n
  simp [NatLt.embedding, Subtype.map]

theorem NatLt.embed_nat_comp_embedding {n m : Nat} (h : m ≤ n) : NatLt.embed_nat ∘ NatLt.embedding h = NatLt.embed_nat := by
  funext x
  simp [NatLt.embedding]
  unfold NatLt.embed_nat
  rfl

theorem NatLt.cast_comp_embedding {n m k : Nat} (hembed : n ≤ m) (heq : m = k) :
     (heq ▸ id) ∘ NatLt.embedding hembed = NatLt.embedding (heq ▸ hembed) := by
  funext x
  subst heq
  simp

@[simp] theorem NatLt.embed_nat_coe (x : NatLt n) : (NatLt.embed_nat x : Nat) = x := by unfold NatLt.embed_nat; rfl
@[simp] theorem NatLt.embedding_nat_coe (x : NatLt n) (h : n ≤ m) : (NatLt.embedding h x : Nat) = x := by unfold NatLt.embedding; rfl

theorem NatLt.embedding_subtype_val_eq_iff :
  Subtype.val ∘ f = Subtype.val ∘ g ↔ NatLt.embedding h ∘ f = NatLt.embedding h' ∘ g := by
  constructor
  . intro h_eq
    funext x
    simp [h_eq]
    have := congrFun h_eq x
    simp at this
    unfold Subtype.map
    apply Subtype.ext
    assumption
  . intro h_eq
    funext x
    simp [h_eq]
    have := congrFun h_eq x
    simp at this
    unfold Subtype.map at this
    simp at this
    assumption


theorem NatLt.embedding_subtype_val_eq_iff_applied :
  (∀ x, (Subtype.val ∘ f) x  = (Subtype.val ∘ g) x ) ↔ (∀ x, (NatLt.embedding h ∘ f) x = (NatLt.embedding h' ∘ g) x) := by
  have := NatLt.embedding_subtype_val_eq_iff (f := f) (g := g) (h := h) (h' := h')
  repeat rw [funext_iff] at this
  assumption


theorem NatLt.embed_nat_subtype_val_eq_iff :
  Subtype.val ∘ f = Subtype.val ∘ g ↔ NatLt.embed_nat ∘ f = NatLt.embed_nat ∘ g := by
  constructor
  . intro h_eq
    funext x
    simp [h_eq]
    have := congrFun h_eq x
    simp at this
    assumption
  . intro h_eq
    funext x
    simp [h_eq]
    have := congrFun h_eq x
    simp at this
    assumption

/- This may be worth completing at some point:

theorem NatLt.induction {k : Nat} {P : NatLt k → Prop}
  (h0 : P ⟨0, sorry⟩)
  (hstep : ∀ (n : NatLt k), P n → n.1 + 1 < k → P ⟨n.1 + 1, sorry⟩)
  : ∀ (n : NatLt k), P n := by
  intro n
  -- First show n.1 is actually a Nat
  have hn_nat : 0 ≤ n.1 := sorry -- This follows from n.1 < k

  -- Now we can use Nat induction
  exact Nat.strong_induction_on (Int.toNat n.1) (λ m hm ↦ sorry)
-/




/-- ## scanr lemmas -/

theorem List.scanr_length {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  List.length (List.scanr f init l) = List.length l + 1 := by
  induction l
  case nil =>
    simp
  case cons hd tl ih =>
    -- apply List.scanr_cons
    rw [List.scanr_cons]
    exact Nat.succ_inj'.mpr ih


theorem List.getElem?_zero_getD_eq_headD {α : Type} (l : List α) :
  l[0]?.getD = l.headD := by
  funext d
  rw [List.headD_eq_head?_getD]
  congr
  rw [List.head?_eq_getElem?]


theorem List.scanr_length_tail {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  List.length ((List.scanr f init l).tail) = List.length l := by
  simp [List.scanr_length]


theorem List.scanr_head_eq_foldr {α β : Type}  (f : α → β → β) (init : β) (hd : α) (tl : List α) :
  let scanlist := List.scanr f init (hd :: tl)
  ∃ (hnonempty: scanlist ≠ []), List.head scanlist hnonempty = f hd (List.foldr f init tl) := by
  simp

theorem List.scanr_headD_eq_foldr {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  (List.scanr f init l).headD init = List.foldr f init l := by
  match l with
  | [] => rfl
  | hd :: tl =>
      rw [List.scanr_cons]
      simp

theorem List.scanr_cons_as_cons_scanr {α β : Type} (f : α → β → β) (init : β) (hd : α) (tl : List α) :
  List.scanr f init (hd :: tl) =
     let scanr_tl := List.scanr f init tl
     (f hd (scanr_tl.headD init)) :: scanr_tl := by
   rw [List.scanr_cons]
   congr
   . induction tl; all_goals simp
