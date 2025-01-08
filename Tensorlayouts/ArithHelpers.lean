import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp

def Nat.prod (l : List Nat) : Nat :=
  List.foldr (fun x acc => x * acc) 1 l

theorem Nat.prod_nil : Nat.prod [] = 1 := by
  unfold Nat.prod
  rw [List.foldr_nil]

theorem Nat.prod_cons : Nat.prod (a :: l) = a * Nat.prod l := by
  unfold Nat.prod
  rw [List.foldr_cons]


def List.inner_prod {α: Type} [Mul α] [Add α] [Zero α] (l : List α) (r : List α) : α :=
   List.sum (List.zipWith (fun x y => x * y) l r)

theorem List.inner_prod_nil_nil {α: Type} [Mul α] [Add α] [Zero α] :
   List.inner_prod [] [] = 0 := by
  simp [List.inner_prod, List.sum_nil, List.zipWith_nil]


theorem List.inner_prod_cons {α: Type} [Mul α] [Add α] [Zero α] (a : α) (l : List α) (b : α) (r : List α) :
   List.inner_prod (a :: l) (b :: r) = a * b + List.inner_prod l r := by
  unfold List.inner_prod
  rw [List.zipWith_cons_cons]
  rw [List.sum_cons]


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


/-- ## NatLT -/

abbrev NatLt (n : Nat) : Type := { idx : Nat // idx < n }

def NatLt.embedding {n m : Nat} (h : n ≤ m) : NatLt n -> NatLt m :=
  fun x => ⟨x.val, Nat.lt_of_lt_of_le x.property h⟩

def NatLt.embed_nat {n : Nat} : NatLt n -> Nat :=
  fun x => x.val

theorem NatLt.embedding_comp {n m k : Nat} (h1 : k ≤ n) (h2 : m ≤ k) : NatLt.embedding h1 ∘ NatLt.embedding h2 = NatLt.embedding (Nat.le_trans h2 h1) := by
  funext n
  simp [NatLt.embedding]

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

--   Eq.rec (motive := fun x h ↦ NatLt k → NatLt x) id hshape_fn



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


theorem List.scanr_length_tail {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  List.length ((List.scanr f init l).tail) = List.length l := by
  simp [List.scanr_length]


theorem List.scanr_head_eq_foldr {α β : Type}  (f : α → β → β) (init : β) (hd : α) (tl : List α) :
  let scanlist := List.scanr f init (hd :: tl)
  ∃ (hnonempty: scanlist ≠ []), List.head scanlist hnonempty = f hd (List.foldr f init tl) := by
  simp

theorem List.scanr_head_eq_foldr_D {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  let scanlist := List.scanr f init l
  List.headD scanlist init = List.foldr f init l := by
  match l with
  | [] => rfl
  | hd :: tl =>
      intro scanlist
      unfold scanlist
      rw [List.scanr_cons]
      simp

theorem List.scanr_cons_as_cons_scanr {α β : Type} (f : α → β → β) (init : β) (hd : α) (tl : List α) :
  List.scanr f init (hd :: tl) =
     let scanr_tl := List.scanr f init tl
     (f hd (scanr_tl.headD init)) :: scanr_tl := by
   rw [List.scanr_cons]
   congr
   . induction tl; all_goals simp
