import Lean

namespace Chapter3

-- 3.3 First Experiments

def square : Int → Int
| x => x * x

#eval square 12

def hword (s : String) : Bool :=
 let rec aux : List Char → Bool
  | [] => false
  | x :: xs => (x == 'h') ∨ aux xs
  aux s.data

#eval hword "hello"
#eval hword "trip"


-- 3.5 Recursion

def gen (n : Nat) : String :=
 match n with
 | Nat.zero => "Sentences can go on"
 | Nat.succ n => gen n ++ " and on"

def genS (n : Nat) : String :=
 gen n ++ "."

#eval genS 3

def reversal (s : String) : String :=
 let rec aux : List Char → List Char
 | [] => []
 | x :: t => (aux t) ++ [x]
 (aux s.data).asString

def reversal' (s : String) : String :=
 s.data.reverse.asString

#eval reversal "hello"

def sonnet18 : String :=
 "Shall I compare thee to a summer's day? \n"
 ++ "Thou art more lovely and more temperate: \n"
 ++ "Rough winds do shake the darling buds of May, \n"
 ++ "And summer's lease hath all too short a date: \n"
 ++ "Sometime too hot the eye of heaven shines, \n"
 ++ "And often is his gold complexion dimm'd; \n"
 ++ "And every fair from fair sometime declines, \n"
 ++ "By chance or nature's changing course untrimm'd; \n"
 ++ "But thy eternal summer shall not fade \n"
 ++ "Nor lose possession of that fair thou owest; \n"
 ++ "Nor shall Death brag thou wander'st in his shade, \n"
 ++ "When in eternal lines to time thou growest: \n"
 ++ "  So long as men can breathe or eyes can see, \n"
 ++ "  So long lives this and this gives life to thee."

def sonnet73 : String :=
 "That time of year thou mayst in me behold
  When yellow leaves, or none, or few, do hang
  Upon those boughs which shake against the cold,
  Bare ruin'd choirs, where late the sweet birds sang.
  In me thou seest the twilight of such day
  As after sunset fadeth in the west,
  Which by and by black night doth take away,
  Death's second self, that seals up all in rest.
  In me thou see'st the glowing of such fire
  That on the ashes of his youth doth lie,
  As the death-bed whereon it must expire
  Consumed with that which it was nourish'd by.
  This thou perceivest, which makes thy love more strong,
  To love that well which thou must leave ere long."


notation "ℕ" => Nat

def count {α : Type} [BEq α] : α → List α → ℕ
| _, [] => 0
| x, y :: ys => if x == y then 1 + count x ys else count x ys

#eval count 'e' "teletransport".toList

def average₁ (xs : List Nat) : Float :=
 (xs.foldl (·  + ·) 0).toFloat / xs.length.toFloat

#eval average₁ $ List.iota 456

def average₂ (xs : List Int) : Lean.Rat :=
 Lean.mkRat (xs.foldl (·  + ·) 0) xs.length

#eval average₂ $ List.iota 456 |>.map Int.ofNat

def _root_.List.prefix [BEq a] (ps : List a) (xs : List a) : Bool :=
  let rec aux : List a → List a → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, x :: xs => p == x ∧ aux ps xs
  aux ps xs

#eval "hello".toList.prefix "hello world".toList

/- Basic Statistics -/

def preprocess : String → String :=
 List.asString ∘
 List.map Char.toLower ∘
 List.filter (! List.elem · "?;:,.".toList) ∘
 String.toList

#eval preprocess sonnet73


section InsertSort

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

def orderedInsert [LE α] (a : α)  : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

def insertionSort [LE α] : List α → List α
  | [] => []
  | b :: l => orderedInsert r b (insertionSort l)

end InsertSort

section

set_option profiler true
set_option trace.profiler.output.pp true
set_option profiler.threshold 2

#eval insertionSort (· ≤ ·) ["white", "yellow", "black"]
#eval insertionSort (· ≤ ·) $ List.iota 1000

end

partial def words₁ (s : String) : List String :=
 let f : Char → Bool := (fun x => x.isWhitespace)
 let rec aux (s : List Char) : List (List Char) :=
   match s.dropWhile f with
   | [] => []
   | s => let (p, r) := s.span (not ∘ f); p :: aux r
 List.map List.asString $ aux s.toList

def words₂ (s : String) : List String :=
  s.split (·.isWhitespace) |>.filter (· ≠ "")

#eval words₁ "hi"
#eval words₁ "\rhello\nworld\t!\n\t"
#eval words₁ " the  greeness of the grass on the other  side "
#eval words₂ " the  greeness of the grass on the other  side "



def process : String → List String :=
  insertionSort (· ≤ ·) ∘ List.eraseDups ∘ words₂

def cnt (s : String) : List (String × Nat) :=
  let as := (process ∘ preprocess) s
  let bs := (words₂ ∘ preprocess) s
  as.map (fun x => (x, count x bs)) |>.filter (·.snd > 1)

#eval cnt sonnet73


/- Finnish Vowel Harmony -/

def db := [('ä', 'a'), ('ö', 'o'), ('y', 'u')]

def back (c : Char) : Char :=
 let m := db.toAssocList'
  match m.find? c with
  | some x => x
  | none => c

def front (c : Char) : Char :=
 let m := db.map (fun x => (x.snd,x.fst)) |>.toAssocList'
 match m.find? c with
 | some x => x
 | none => c

def appendSuffixF : String → String → String
  | stem, suffix => stem ++ suffix.map (vh stem)
 where
  vh s :=
   if s.any (· ∈ "aou".toList) then back
   else if s.any (· ∈ ['ä', 'ö', 'y']) then front else id

#eval appendSuffixF "pouta" "na"
#eval appendSuffixF "koti" "na"
#eval appendSuffixF "pöytä" "na"


/- Swedish morphology -/

inductive DeclClass where
  | One
  | Two
  | Three
  | Four
  | Five

def swedishVowels := ['a','i','o','u','e','y','ä','å','ö','ø']

def _root_.String.init (s : String) : String :=
  s.dropRight 1

def swedishPlural : String → DeclClass → String
 | noun, d => match d with
  | DeclClass.One   => noun.init ++ "or"
  | DeclClass.Two   => noun.init ++ "ar"
  | DeclClass.Three => if noun.back ∈ swedishVowels
                       then noun ++ "r"
                       else noun ++ "er"
  | DeclClass.Four  => noun ++ "n"
  | DeclClass.Five  => noun

#eval swedishPlural "ficka" DeclClass.One
#eval swedishPlural "blomma" DeclClass.One
#eval swedishPlural "pojke" DeclClass.Two
#eval swedishPlural "ko" DeclClass.Three
#eval swedishPlural "rad" DeclClass.Three
#eval swedishPlural "åpple" DeclClass.Four
#eval swedishPlural "hus" DeclClass.Five

end Chapter3
