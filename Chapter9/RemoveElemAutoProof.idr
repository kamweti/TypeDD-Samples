import Data.Vect
import Data.Vect.Elem
import Chapter9.RemoveElem

removeElemAutoProof : {len                  : _}                              ->
                      (needle               : elemType)                       ->
                      (haystack             : Vect (S len) elemType)          ->
                      {auto proof_          : Elem needle haystack }          ->
                      Vect len elemType
removeElemAutoProof needle haystack {proof_} = removeElem needle haystack proof_

{-
    TypeDD-Samples (master) ✗  idris2 Chapter9/RemoveElemAutoProof.idr
    Main> removeElemAutoProof 3 [1, 2, 3, 4, 5]
    Main> :t removeElemAutoProof 3 [1, 2, 3, 4, 5]
    Main> removeElemAutoProof 3 [1, 2, 4, 5]
-}