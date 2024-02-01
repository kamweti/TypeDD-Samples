import Data.Vect
import Data.Vect.Elem

removeElem : {len : _}                              ->
             (needle    : elemType)                 ->
             (hayStack  : Vect (S len) elemType)    ->
             (proof_    : Elem needle hayStack)     -> Vect len elemType
removeElem needle (needle :: haystack) Here = haystack
removeElem {len = 0} needle (y :: []) (There later) = absurd later
removeElem {len = (S k)} needle (y :: xs) (There later) = y :: removeElem needle xs later
