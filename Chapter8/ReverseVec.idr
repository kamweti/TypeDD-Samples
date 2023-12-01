import Data.Vect

myReverse : Vect len item -> Vect len item
myReverse [] = []
myReverse {len = S len} (x :: xs) =
    let rev_xs = myReverse xs
        result = rev_xs ++ [x]
            in
                rewrite (plusCommutative 1 len)
            in result

reverseProof : Vect (plus len 1) item -> Vect (S len) item
reverseProof {len} ys = rewrite plusCommutative 1 len in ys

myReverseSecondAttempt : Vect len item -> Vect len item
myReverseSecondAttempt [] = []
myReverseSecondAttempt (x :: xs) = reverseProof (myReverseSecondAttempt xs ++ [x])