import Data.Vect
import Decidable.Equality

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

notInEmpty : Elem needle [] -> Void
notInEmpty Here impossible
notInEmpty (There later) impossible

notInTail : (notThere : Elem needle xs -> Void) ->
            (notHere : (needle = x) -> Void) -> Elem needle (x :: xs) -> Void
notInTail notThere notHere Here = notHere Refl
notInTail notThere notHere (There later) = notThere later

isElem : DecEq elemType => (needle : elemType) -> (haystack : Vect len elemType) -> Dec (Elem needle haystack)
isElem needle [] = No notInEmpty
isElem needle (x :: xs) = case decEq needle x of
                              (Yes Refl) => Yes Here
                              (No notHere) => case isElem needle xs of
                                                  (Yes prf) => Yes (There prf)
                                                  (No notThere) => No (notInTail notThere notHere)