import Lean

namespace IR.Chapter1

/- indexing -/

def words (s : String) : List String :=
  s.split (fun x => x.isWhitespace || ".,;:!?«»()[]“”".contains x)
  |>.filter (· ≠ "") |>.map String.toLower

def preProc (s : String) (n : Nat) : Array (String × Nat) :=
  words s |>.toArray |>.map (λ x => (x, n))

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

def indexDoc
 (dict : Lean.HashMap String (List Nat))
 (pairs : Array (String × Nat)) : Lean.HashMap String (List Nat) :=
 Array.foldl insertPair dict pairs

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
      mdict ← indexFile mdict (folder.join s!"{d}.raw") d
    return mdict

/- query execution -/

inductive Query where
 | w : String → Query
 | and : Query → Query → Query
 | or : Query → Query → Query
 deriving Repr

def intersect : List Nat → List Nat → List Nat
 | [], _ => []
 | _, [] => []
 | a :: l1, b :: l2 =>
   if     a == b then a :: intersect l1 l2
   else if a < b then intersect l1 (b :: l2)
   else intersect (a :: l1) l2

/- qual complexidade? podemos melhorar performance? -/
def union (a : List Nat) (b : List Nat) : List Nat :=
   (a ++ b).eraseDups

def eval (q: Query) (idx : Lean.HashMap String (List Nat)) : List Nat :=
  match q with
  | Query.w w => match idx.find? w with
    | none => []
    | some l => l
  | Query.and q1 q2 => intersect (eval q1 idx) (eval q2 idx)
  | Query.or q1 q2 => union (eval q1 idx) (eval q2 idx)

/- testing -/

def indexing : IO (Lean.HashMap String (List Nat)) := do
 let docs := [1,2,3,4,5,6,7,8,9,10,11,12,13,100,101,102,103,104,105,106,107,108,109,110]
 let idx ← indexFiles Lean.HashMap.empty "/Users/ar/r/cpdoc/dhbb-nlp/raw" docs
 return idx

-- #eval Functor.map (·.toList |>.length) indexing
-- #eval (·.toList) <$> indexing

def mainInterface (idx : IO (Lean.HashMap String (List Nat))) (q : Query)
 : IO (List Nat) := do
 let db ← idx
 return eval q db

def dhbb : Query → IO (List Nat) := mainInterface indexing

#eval dhbb (Query.and (Query.or (Query.w "presidente") (Query.w "senador"))
                      (Query.w "voto"))


end IR.Chapter1
