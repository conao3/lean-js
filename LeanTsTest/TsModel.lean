import LeanTsLib.Ts

namespace LeanTsTest.TsModel

def indexInt (xs : List Int) (i : Int) : Option Int := Ts.index xs i

def getInt (xs : List Int) (i : Int) : Except Ts.Exc Int := Ts.get xs i

def unwrapInt (o : Option Int) : Except Ts.Exc Int := Ts.unwrap o

def floorDiv (a b : Int) : Except Ts.Exc Int := Ts.floorDiv a b

def truncDiv (a b : Int) : Except Ts.Exc Int := Ts.truncDiv a b

def rem (a b : Int) : Except Ts.Exc Int := Ts.rem a b

def range (a b : Int) : List Int := Ts.range a b

def abs (a : Int) : Int := Ts.abs a

def lengthInt (xs : List Int) : Int := Ts.length xs

def strLength (s : String) : Int := Ts.strLength s

def startsWith (s t : String) : Bool := Ts.startsWith s t

def endsWith (s t : String) : Bool := Ts.endsWith s t

def includes (s t : String) : Bool := Ts.includes s t

def strInt (n : Int) : String := Ts.str n

def strBool (b : Bool) : String := Ts.str b

def error (name message : String) : Except Ts.Exc Int := throw (Ts.Exc.error name message)

end LeanTsTest.TsModel
