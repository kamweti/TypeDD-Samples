import Data.Vect
import Decidable.Equality

-- -- uncomment to see the error
-- removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
-- removeElem value (x :: xs) = case decEq value x of
--                                 Yes pr => xs
--                                 No contra => x :: removeElem value xs
