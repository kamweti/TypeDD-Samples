import Data.Vect

some_proof_0 : Vect m elemType -> Vect (plus m 0) elemType
some_proof_0 {m} xs = rewrite plusZeroRightNeutral m  in xs

some_proof_1 : Vect (S (plus m len)) elemType -> Vect (plus m (S len)) elemType
some_proof_1 {m} {len} xs = rewrite sym
                                (plusSuccRightSucc m len) in xs

append : Vect n elemType -> Vect m elemType -> Vect (m + n) elemType
append [] ys = some_proof_0 ys
append (x :: xs) ys = some_proof_1 (x :: append xs ys)
