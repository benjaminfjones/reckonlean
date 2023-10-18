def hello := "world"

#eval String.append "hello" ", world"
#check hello
/- #eval String.append "hello" -/

def addOne (n: Nat) : Nat := n + 1

structure Point where
  x: Float
  y: Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin

def zeroX (p: Point) : Point := { p with x := 0.0 }

#eval Point.mk 0 1
#eval Point.mk 0 0
