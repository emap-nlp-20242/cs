import Lean

def doc1 : String := "I did enact Julius Caesar: I was killed i’ the
 Capitol; Brutus killed me."

def doc2 : String := "So let it be 2024 with Caesar. The noble Brutus hath
 told you Caesar was ambitious:"

def words (s : String) : List String :=
  s.split (fun x => x.isWhitespace || ".,;:!?«»()[]“”".contains x)
   |>.filter (· ≠ "") |>.map String.toLower

def preProc (s : String) (n : Nat) : Array (Prod String Nat) :=
  words s |>.toArray |>.map (·, n)

/-
instance : Ord (Prod String Nat) where
  compare a b := (compare a.1 b.1).then (compare a.2 b.2)
-/
def test := (preProc doc1 1) ++ (preProc doc2 2)

/- Can it be simpler? -/
#eval test.qsort (fun x y => Ordering.isLT $ @compare _ lexOrd x y)
#eval test.qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 < y.2))


def orderedInsert [BEq α] [Ord α] : α → List α → List α
  | a, [] => [a]
  | a, b :: l =>
    if a == b then
     b :: l
    else if (compare a b).isLT then
     a :: b :: l
    else
     b :: orderedInsert a l

def insertPair [BEq α] [BEq β] [Ord β] [Hashable α]
  (m : Lean.HashMap α (List β)) (p : α × β) : Lean.HashMap α (List β)
  := m.insert p.1 (match m.find? p.1 with
    | none => [p.2]
    | some l => orderedInsert p.2 l)

/-
def orderedInsert : Nat → List Nat → List Nat
  | a, [] => [a]
  | a, b :: l => if a ≤ b
    then a :: b :: l else b :: orderedInsert a l

def insertPair (m : IndexMap) (p : String × Nat) : IndexMap
  := m.insert p.1 (match m.find? p.1 with
    | none => [p.2]
    | some l => orderedInsert p.2 l)
-/


def indexDoc
 (dict : Lean.HashMap String (List Nat))
 (pairs : Array (String × Nat)) : Lean.HashMap String (List Nat) :=
 Array.foldl insertPair dict pairs

#eval indexDoc Lean.HashMap.empty test |>.toList

def indexFile (dict : Lean.HashMap String (List Nat))
  (filename : System.FilePath) (doc : Nat)
  : IO (Lean.HashMap String (List Nat)) := do
  let txt ← IO.FS.readFile filename
  return indexDoc dict (preProc txt doc)

def indexFiles
  (dict : Lean.HashMap String (List Nat))
  (folder : System.FilePath) (docs : List Nat)
  := do
    let mut mdict := dict
    for d in docs do
      mdict ← indexFile mdict (folder.join s!"{d}.text") d
    return mdict.toList


def docs := [10,100,200,12,44,20,13,202,201,301,310,403]

#eval indexFiles Lean.HashMap.empty "/Users/ar/r/cpdoc/dhbb/text" docs

inductive Query where
 | w : String → Query
 | and : Query → Query → Query
 deriving Repr

#eval Query.and (Query.w "teste") (Query.w "agora")
