import Lean

namespace IR.Chapter1

/- indexing -/

def words (s : String) : List String :=
  s.split (fun x => x.isWhitespace || ".,;:!?«»()[]“”".contains x)
  |>.filter (· ≠ "") |>.map String.toLower

def insertSorted [BEq α] [Ord α] : α → List α → List α
  | a, [] => [a]
  | a, b :: l =>
    if a == b then
     b :: l
    else if (compare a b).isLT then
     a :: b :: l
    else
     b :: insertSorted a l

def insertPair [BEq α] [BEq β] [Ord β] [Hashable α]
  (m : Lean.HashMap α (List β)) (p : α × β) : Lean.HashMap α (List β)
  := m.insert p.1 (match m.find? p.1 with
    | none => [p.2]
    | some l => insertSorted p.2 l)

def indexDoc
 (dict : Lean.HashMap String (List Nat)) (txt : String) (doc : Nat)
 : Lean.HashMap String (List Nat) :=
 Array.foldl insertPair dict $ (words txt) |>.map ((· , doc)) |>.toArray

def indexFiles
  (dict : Lean.HashMap String (List Nat))
  (docs : Array System.FilePath) : IO (Lean.HashMap String (List Nat))
  := do
    let mut mdict := dict
    let enum := (fun as => (List.iota as.size |>.reverse.toArray).zip as)
    for d in enum docs do
      let txt ← IO.FS.readFile d.2
      mdict := indexDoc mdict txt d.1
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

def union₁ (a b : List Nat) (acc : List Nat) : List Nat :=
 match a, b with
 | [], l2 => l2.reverse ++ acc
 | l1, [] => l1.reverse ++ acc
 | a :: l1, b :: l2 =>
   if     a == b then union₁ l1 l2 (a :: acc)
   else if a < b then union₁ l1 (b :: l2) (a :: acc)
   else union₁ (a :: l1) l2 (b :: acc)

def union (a b : List Nat) : List Nat :=
  (union₁ a b []).reverse

def eval (q: Query) (idx : Lean.HashMap String (List Nat)) : List Nat :=
  match q with
  | Query.w w => match idx.find? w with
    | none => []
    | some l => l
  | Query.and q1 q2 => intersect (eval q1 idx) (eval q2 idx)
  | Query.or q1 q2 => union (eval q1 idx) (eval q2 idx)


/- testing -/

def indexing : IO (Lean.HashMap String (List Nat)) := do
 let files ← System.FilePath.walkDir "/Users/ar/r/cpdoc/dhbb-nlp/raw"
 let names := files.filter (fun x => match x.fileName with
   | none => false
   | some nm => nm.startsWith "7" && nm.endsWith "raw")
 let idx ← indexFiles Lean.HashMap.empty names
 return idx

#eval Functor.map (·.toList |>.length) indexing
#eval (·.toList) <$> indexing

def mainInterface (idx : IO (Lean.HashMap String (List Nat))) (q : Query)
 : IO (List Nat) := do
 let db ← idx
 return eval q db

def dhbb : Query → IO (List Nat) := mainInterface indexing

#eval dhbb (Query.and (Query.or (Query.w "licitação") (Query.w "compra"))
                      (Query.w "presidente"))


end IR.Chapter1
