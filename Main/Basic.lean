#eval 1+1
#eval 1+1*3
#eval String.append "Hello" ", world!"
#eval String.append "great " (String.append "oak " "tree")
#eval String.append "it is " (if 1 > 2 then "Yes" else "No")
#check 1-2

def hello := "Hello"

def add1 (n : Nat) : Nat := n+1
#eval add1 3

def maxi (n : Nat) (m : Nat) : Nat :=
  if n < m then m else n

#eval maxi 3 5

------------------------------aula 24/03/25
#check String.append "hi"

structure Point where
  --mkPoint :: muda o nome do construtor padrão mk.
  x : Float
  y : Float
deriving Repr -- tanto faz

def origin : Point := {x := 0.0, y := 0.0}
def point1 : Point := {x := 5.0, y := 5.0}

#eval origin
#eval origin.x
#check Point.mk

def a1 := 1
#eval a1

def addPoints (p1 p2 : Point) : Point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

#eval zeroX point1

def joinStringsWith (s1 s2 s3: String) : String :=
  String.append s1 (String.append s2 s3)

#check joinStringsWith
#eval joinStringsWith "hi, " "how " "are you?"

def Str : Type := String


------------------------------ defining curry and uncurry
def curry (f: α × β → γ) : (α → β → γ) :=
  λa => λb => f (a,b) -- λa.λb.f (a, b)

def uncurry (f: α → β → γ) : (α × β → γ) :=
  λ (a,b) => f a b


------------------------------aula 09/04/25
