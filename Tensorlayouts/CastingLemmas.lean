import Tensorlayouts.ArithHelpers

theorem id_heq_casting_lemma (n m : Nat) (h : n = m) (x : NatLt n) :
  HEq x ((Eq.rec (motive := fun x _ => ((NatLt n) -> (NatLt x))) id h) x) := by
  subst h
  simp

theorem id_casting_lemma (k k' : Nat) (h : k = k') (x : NatLt k) (y : NatLt k') (hxy : (y : Nat) = (x : Nat)) :
  y = ((Eq.rec (motive := fun x _ => ((NatLt k) -> (NatLt x))) id h) x) := by
  subst h
  simp
  apply Subtype.ext
  assumption
