import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp

def Nat.prod (l : List Nat) : Nat :=
  List.foldr (fun x acc => x * acc) 1 l

def List.inner_prod {α: Type} [Mul α] [Add α] [Zero α] (l : List α) (r : List α) : α :=
   List.sum (List.zipWith (fun x y => x * y) l r)

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

theorem PosInt.mul_comm (a b : PosInt) : a * b = b * a := by
  unfold HMul.hMul
  unfold instHMulPosInt
  simp
  have h : a.val * b.val = b.val * a.val := by
    exact Nat.mul_comm a.val b.val
  simp [h]


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
