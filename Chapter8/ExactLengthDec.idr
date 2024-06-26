import Decidable.Equality

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

exactLength : {m : _}
               -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect m a)
exactLength {m} len input = case decEq m len of
                              Yes Refl => Just input
                              No contradiction => Nothing