import Data.Vect
import Data.Vect.Elem

removeElem : {len : _}                              ->
             (needle    : elemType)                 ->
             (haystack  : Vect (S len) elemType)    ->
             (proof_    : Elem needle haystack)     -> Vect len elemType
removeElem needle (needle :: haystack) Here = haystack
removeElem {len = 0} needle (y :: []) (There later) = absurd later
removeElem {len = (S k)} needle (y :: xs) (There later) = y :: removeElem needle xs later

{-
    TypeDD-Samples (master) ✗  idris2 Chapter9/RemoveElem.idr
    Main> :let needle : Int
    Main> needle = 3
    Main> :let haystack : Vect 5 Int
    Main> haystack = [1, 2, 3, 4, 5]
    Main> :let proofNeedleExistsInHaystack : Elem needle haystack
    Main> proofNeedleExistsInHaystack = Elem needle haystack
    Main> removeElem needle haystack proofNeedleExistsInHaystack
    Main> :t removeElem needle haystack proofNeedleExistsInHaystack
    removeElem needle haystack proofNeedleExistsInHaystack : Vect 4 Int
-}

{-
    Alternative containing a auto proof

    ```
        removeElem : {len            : _}                             ->
                    (needle         : elemType)                       ->
                    (hayStack       : Vect (S len) elemType)          ->
                    {auto proof_    : Elem needle hayStack}           -> Vect len elemType
        removeElem needle (needle :: haystack) {proof_ = Here}                    = haystack
        removeElem {len = 0} needle (y :: []) {proof_ = There later}              = absurd later
        removeElem {len = (S k)} needle (y :: xs) {proof_ = There later}          = y :: removeElem needle xs
    ```
 -}