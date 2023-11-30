data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat 0 0 = Just Refl
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (cong S x)

exactLength : {m : _}
               -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect m a)
exactLength {m} len input = case checkEqNat m len of
                              Nothing => Nothing
                              (Just x) => Just input