natCannotEqualSuccessor : (x : Nat) -> (x = S x) -> Void
natCannotEqualSuccessor _ Refl impossible
