
namespace Chapter3


def rotations (s : String) : List String :=
 List.map (λ n => s.drop n ++ s.take n) (List.range s.length)

#eval rotations "fi*mo*er*ble$"

def tails : List a → List (List a)
| [] => [[]]
| m@(_ :: xs) => m :: tails xs

def grams (n : Nat) (s : String) : List String :=
 if n > s.length then
  []
 else
  List.filter (fun x => x.length == n) ∘ List.map (fun x => x.take n)
   $ (tails s.toList) |>.map (fun x => x.asString)

#eval grams 3 "recuperação"


end Chapter3
