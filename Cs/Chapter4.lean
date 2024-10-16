import Lean

/- Chapter 4-/

/-
1. Grammars for Games
-/

-- Sea Battle

inductive Column
| A | B | C | D | E | F | G | H | I | J

inductive Row
| r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10

inductive Attack
| attack (col : Column) (row : Row)

inductive Ship
| battleship
| frigate
| submarine
| destroyer

-- Para usar o #eval em algum jogo
instance : ToString Ship :=
⟨fun s =>
  match s with
  | Ship.battleship => "Battleship"
  | Ship.frigate => "Frigate"
  | Ship.submarine => "Submarine"
  | Ship.destroyer => "Destroyer"⟩

/-
Exercise 4.1
Revise the grammar in such a way that it is made explicit in the grammar
rules that the game is over once one of the players is defeated.-/
inductive GameOver
| player1_wins
| player2_wins

inductive Reaction
| missed
| hit (ship : Ship)
| sunk (ship : Ship)
| lost_battle
| game_over (result : GameOver)

inductive Turn
| turn (atk : Attack) (react : Reaction)

-- Possível jogo
def game_sequence : List Turn :=
[
  Turn.turn (Attack.attack Column.C Row.r5) Reaction.missed,
  Turn.turn (Attack.attack Column.A Row.r1) (Reaction.sunk Ship.destroyer),
  Turn.turn (Attack.attack Column.F Row.r7) (Reaction.game_over GameOver.player1_wins)
]

-- função para ver o resultado de um jogo
def last_turn_result (turns : List Turn) : String :=
  match turns.reverse.head? with
  | some (Turn.turn _ (Reaction.missed)) => "Missed"
  | some (Turn.turn _ (Reaction.hit ship)) => "Hit " ++ toString ship
  | some (Turn.turn _ (Reaction.sunk ship)) => "Sunk " ++ toString ship
  | some (Turn.turn _ (Reaction.lost_battle)) => "Lost Battle"
  | some (Turn.turn _ (Reaction.game_over GameOver.player1_wins)) => "Game Over: Player 1 Wins"
  | some (Turn.turn _ (Reaction.game_over GameOver.player2_wins)) => "Game Over: Player 2 Wins"
  | none => "No turns available"

#eval last_turn_result game_sequence

/-Exercise 4.2
Revise the grammar in order to guarantee that a game has at most four turns.
-/

/-Exercise 4.3
Write your own grammars for chess and bingo.
-/

inductive Board_x
  | a | b | c | d | e | f | g | h

inductive Board_y
  | y1
  | y2
  | y3
  | y4
  | y5
  | y6
  | y7
  | y8

inductive Piece
| king
| queen
| rook
| bishop
| knight
| pawn

inductive Color
| white
| black

-- Inductive Move ? Como implementar os movimentos permitidos de cada peça ?
