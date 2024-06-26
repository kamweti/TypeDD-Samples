zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

succNum1EqSuccNum2 : (contradiction: (num1 = num2 -> Void)) -> (S num1 = S num2) -> Void
succNum1EqSuccNum2 contradiction Refl = contradiction Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc
checkEqNat (S k) 0 = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                            Yes prf => Yes (cong S prf)
                            No contradiction => No (succNum1EqSuccNum2 contradiction)