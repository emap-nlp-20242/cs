import Lean

namespace Chapter3

-- 3.3 First Experiments

/- página 35
Calcular quantos dias tem um ano bissexto
-/
#eval 366 * 24 * 60 * 60

/- página 36
Exercise 3.1
Try out a few calculations using * for multiplication, + for addition, - for
subtraction, ^ for exponentiation, / for division. By playing with the system,
find out what the precedence order is among these operators

Sugestão: Fazer demontrações de algumas das propriedades de cada operação
a + b = b + a
-/
#eval (2+3)^4
/-
Exercise 3.2
How much is 2^3^4? Does the interpreter read this as (2^3)^4 or as
2^(3^4)?

Answer: 2^3^4 is interpreted as 2^(3^4)
-/
#eval 2^3^4
#eval (2^3)^4
#eval 2^(3^4)

-- Usando expressão lambda
#eval (λ x => x * x) 4

-- definindo função
def square : Int → Int
  | x => x * x
#eval square (-3)

#eval square (square 2)

#eval square (square (square 2))

/- página 37
[’H’,’e’,’l’,’l’,’o’,’ ’,’W’,’o’,’r’,’l’,’d’,’!’]

’H’:’e’:’l’:’l’:’o’:’ ’:’w’:’o’:’r’:’l’:’d’:’!’:[]
Exercise 3.3
The colon : in the last example is an operator. Can you see what its type is?
-/

def hword (s : String) : Bool :=
 let rec aux : List Char → Bool
  | [] => false
  | x :: xs => (x == 'h') ∨ aux xs
  aux s.data

#eval hword "hello"
#eval hword "trip"
#eval hword "shirimptoast"

/- página 38
1. Dúvida
Infix operation and Prefix operation

Exercise 3.4
Which property does (>3) denote? And which property does (3>) denote?
-/

-- 3.4 Type Polymorphism
-- Implicit Arguments (Functional Programming in Lean 1.6 Polymorphism )
def Identity {α : Type} (x : α) : α := x
#eval Identity 4
#check (Identity)
#eval Identity (hword "haskel")
#eval Identity (hword "lean")
#eval (Identity hword) "haskel"
#eval (Identity hword) "lean"

#eval [2,3] ++ [4,7]
#eval "Hello" ++ " World!"

-- 3.5 Recursion

def gen (n : Nat) : String :=
 match n with
 | Nat.zero => "Sentences can go on"
 | Nat.succ n => gen n ++ " and on"
/-
def gen : Nat → String
  | 0 => "Sentences can go on"
  | .succ n => gen n ++ ", and on"
-/
def genS (n : Nat) : String :=
 gen n ++ "."

 #eval genS 3

def story (k : Nat) : String :=
  match k with
  | Nat.zero => "Let’s cook and eat that final missionary, and off to bed."
  | Nat.succ k => "The night was pitch dark, mysterious and deep. "
      ++ "Ten cannibals were seated around a boiling cauldron. "
      ++ "Their leader got up and addressed them like this: ’"
      ++ story (k) ++ "’"

#eval story 2

/- página 41
Exercise 3.5
What happens if you ask for putStrLn (story (-1))? Why?
Answer:

Exercise 3.6
Why is the definition of ‘GNU’ as ‘GNU’s Not Unix’ not a recursive definition?
-/

-- 3.6 List Types and List Comprehension

/- página 42
in Haskel
[0 ..] ← Lista infinita   ['a' .. 'g'] ← [ 'a' , 'b' , ... , 'f' , 'g']
Slice in list, like [1 .. 42] ⇒ [1, 2, 3, ... , 41, 42]
def numbers : List Nat := [1 .. 42]
#eval numbers

def oddslessthanten : List Nat :=  [ n | n ← [1 .. 10] , odd ]
#eval oddslessthanten
-/

-- 3.7 List processing with map and filter

def sum (α : Nat) ( β : Nat ) : Nat :=
  α + β

def NatUnderTen : List Nat := [1, 2 ,3 ,4 ,5 ,6 ,7 ,8 ,9 ,10]
#eval NatUnderTen.map (sum 1)

def Adjectives : List String := [ "friendly" , "believable" ]
#eval (Adjectives).map ("un".append)

#eval ["fish","and","chips"].map hword

#eval NatUnderTen.filter (· % 2 == 0)

-- 3.8 Function Composition, Conjunction, Disjunction, Quantification

-- Apresento uma definição para composição de funções
def comp {α β γ : Type} (f : β → γ) (g : α → β) : α → γ := λ x =>  f (g x)

def cubic (a : Int ) : Int :=
  a * a * a
#eval cubic 2
#eval comp (square) (cubic) 2


-- Utilizando composição com operador padrão do L∃AN
def f : Nat → Nat := λ x => x + 1
def g : Nat → Nat := λ x => x * 2
#eval (f ∘ g) 3


-- Definições de any e all no Lean Padrão
def any : List α → (α → Bool) → Bool
  | [], _ => false
  | h :: t, p => p h || any t p

def all : List α → (α → Bool) → Bool
  | [], _ => true
  | h :: t, p => p h && all t p

-- Exemplos
#eval all ["fish","and","chips"] hword
#eval ["fish","and","chips"].all hword

-- 3.9 Type Classes
-- Definição not equal
def neq {α : Type} [DecidableEq α] (x y : α) : Bool := x ≠ y
/- página 46
Exercise 3.7
Check the type of the function (\ x y -> x /= y) in Haskell. What do
you expect? What do you get? Can you explain what you get?
-/
#check (neq)

/-Exercise 3.8
Is there a difference between (\ x y -> x /= y) and (/=)?
-/

/- Exercise 3.9
Check the type of the function composition all . (/=). If you were to
give this function a name, what name would be appropriate?
-/
def list_all_neq {α : Type} [DecidableEq α] (x : α) (l : List α) : Bool :=
  l.all (λ y => x ≠ y)

#check (list_all_neq)

/- Exercise 3.10
Check the type of the function composition any . (==). If you were to
give this function a name, what name would be appropriate?
-/
def list_any_eq {α : Type} [DecidableEq α ] (x: α )(l : List α ) : Bool :=
  l.all (λ y => x ≠ y)

#check (list_any_eq)

/- Obs:
Esses exercicios do livro tentam ilustrar o fato da restrição [DecidableEq α ] necessária
para as funções que verificam igualdade e/ou desigualdade
-/

/- Exercise 3.11
How would you go about testing two infinite strings for equality?
-/

/- Exercise 3.12
Use min to define a function minList :: Ord a => [a] -> a for
computing the minimum of a non-empty list.
-/

def minimum? [Min α] : List α → Option α
  | []    => none
  | a::as => some <| as.foldl min a

#eval minimum? [ 8 , 5 , 4 , 2 , 3 , 1]

def minList { α : Type }[LT α] [DecidableRel (@LT.lt α _)] (l : List α) : Option α :=
  match l with
| [] => none
| (x::xs) => some (xs.foldl (λ acc y => if y < acc then y else acc) x)

#eval minList [ 9 , 9 , 4 , 7 , 0]

/- Exercise 3.13
Define a function delete that removes an occurrence of an object x from
a list of objects in class Eq. If x does not occur in the list, the list remains unchanged.
If x occurs more than once, only the first occurrence is deleted
-/

def delete {α : Type} [DecidableEq α]  (lista : List α ) (x : α) : List α  :=
match lista with
  | [] => lista
  | (y::ys)  => if x = y then ys else y :: delete ys x

#eval delete [1, 2, 3, 4, 3] 2
#eval delete [1, 2, 3, 4] 3

-- How would you need to change delete in order to delete every occurence of x?
def delete_all {α : Type} [DecidableEq α]  (lista : List α ) (x : α) : List α  :=
match lista with
  | [] => lista
  | (y::ys)  => if y = x then delete_all ys x else y :: (delete_all ys x)

#eval delete_all [1, 1, 1 ,2 ,5 , 9, 8 ,1 ,2 ,5] 1

/- Exercise 3.14
Define a function srt :: Ord a => [a] -> [a] that implements the
above. Use the function minList from Exercise 3.12.
-/
/-
def minNat  (l : List Nat) : Nat :=
  []

def sortNat (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x::xs => l.minimum?

def srt {α : Type} [Min α ] (k : List α ): List α :=
  match k with
| [] => []
| x::xs => x.minimum? :: srt xs
-/

-- 3.10 Strings and Texts
def reversal₁ : List a → List a
 | [] => []
 | x :: xs => reversal₁ xs ++ [x]

def reversal (s : String) : String :=
 (reversal₁ s.data).asString

theorem reverse_append' {α : Type} :
  ∀ xs ys : List α,
    reversal₁ (xs ++ ys) = reversal₁ ys ++ reversal₁ xs := by
  intro xs ys
  induction xs with
  | nil => simp [reversal₁]
  | cons x xs ih =>
    simp [reversal₁]
    simp [ih]

@[simp] theorem reverse_append {α : Type} :
  ∀ xs ys : List α,
    reversal₁ (xs ++ ys) = reversal₁ ys ++ reversal₁ xs
 |      [], ys => by simp [reversal₁,List.nil_append]
 | x :: xs, ys => by
  simp [reversal₁]
  simp [reverse_append xs]

theorem rev_rev {a : Type} (xs : List a) :
  reversal₁ (reversal₁ (xs)) = xs := by
  induction xs with
  | nil => simp [reversal₁.eq_1]
  | cons x xs ih =>
    simp [reversal₁,ih]

#eval reversal "hello"
#eval  reversal (reversal "Chomsky")

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

#eval count 'e' sonnet73.toList
#eval count 'e' "teletransport".toList

def average₁ (xs : List Nat) : Float :=
 (xs.foldl (·  + ·) 0).toFloat / xs.length.toFloat

#eval average₁ $ List.iota 456

def average₂ (xs : List Int) : Lean.Rat :=
 Lean.mkRat (xs.foldl (·  + ·) 0) xs.length

#eval average₂ $ List.iota 456 |>.map Int.ofNat

/- Exercise 3.16 página 51
Write a function to compute the average word length in Shakespeare’s sonnets 18 and 73.
You can use filter (‘notElem‘ "?;:,.") to get rid of the interpunction signs.
The predefined function length (from the List module) gives the length of a
list.
-/
def words (s : String) : List String :=
  s.split (fun x => x.isWhitespace || ".,;:!?«»()[]“”".contains x)
  |>.foldr step []
  where
    step w acc := if w ≠ "" then w.toLower :: acc else acc

#eval words sonnet18
#eval (words sonnet18).length

def count_lenght_word (listwords : List String) : List Nat :=
  listwords.map (λ s => s.length)

#eval count_lenght_word (words sonnet18)

def sum_list_elemnts (listNat : List Nat) : Nat :=
  listNat.foldl (λ acc x => acc + x) 0

#eval sum_list_elemnts (count_lenght_word (words sonnet18))

def average_word_length (text : String) : Nat :=
  sum_list_elemnts ( (count_lenght_word (words text))) / ((words sonnet18).length)

#eval average_word_length sonnet73

-- Verificar, acho que tem algum erro

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
