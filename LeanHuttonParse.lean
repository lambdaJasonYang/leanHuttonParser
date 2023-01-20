/- Hutton Monadic Parser -/

namespace HuttonParser

/- Parser is a singleton product type containing
a `parse` function.
`parse` returns either a singleton list representing success
or a empty list representing failure.
-/

structure Parser (T: Type) : Type  where 
  parse : (String -> List (T ×  String))

open Parser 

#check Parser.mk (λ x => [('a',x)])


/- 3 Parser primitives: result, zero, item -/

def result {T : Type } : T -> Parser T := 
  λ v => Parser.mk $ λ inp => [(v, inp)]

def zero {T: Type } : Parser T :=
  Parser.mk $ λ inp => []

def item : Parser Char :=
  Parser.mk λ x => 
    match String.data x with
    | [] => []
    | x::xs => [(x,String.mk xs)] 

#eval (result 'f').parse "hfaiweh"
#eval item.parse "awefawe"




def concatMap {S T: Type} : (S -> List T) -> List S -> List T := 
λ f s => 
  match s with
  | [] => []
  | x::xs => (f x)++(concatMap f xs)

#eval String.append "d"  "da"

--demo of how concatMap wrt to Parsers
#reduce concatMap (λ (p, x) => [(p, p x)]) [(λ v => v + 4 ,24)]


instance : Functor Parser where 
  map := λ f (Parser.mk st) => Parser.mk (λ stream => List.map (λ(a,b) => (f a, b)) (st stream))


instance : Monad Parser where
  pure {T : Type} : T -> Parser T  :=
λ a => Parser.mk (λ s => [(a,s)])
  bind {S T : Type} : Parser S -> (S -> Parser T) -> Parser T :=
λ p f => Parser.mk (λinp => concatMap (λ (v,inp2) => (f v).parse inp2) $ p.parse inp )
/-
-- concatMap is just used to flatten the singleton array, 
-- alternative and equivalent bind function is defined below (which i find easier to understand):
λ p f => Parser.mk (λinp =>  (match p.parse inp with  
                                      | [(v,inp2)] => (f v).parse inp2 
                                      | _ => [])
                                      )
-/


#check item >>= (λ x => item)
#eval item.parse "hi"
#eval (item >>= (λ x => result x)).parse "hi"
#eval (item >>= λ x => item >>= λ y => result [x,y]  ).parse "hia"


instance :  Applicative Parser where 
   pure := pure --this pure is taken from the Monad Parser's defined pure above
   seq := λ p q => p >>= (λ x => ((q ⟨⟩) >>= (λ y => result (x y))))

def sat : (Char -> Bool) -> Parser Char :=
  λ p => item >>= (λ x => if p x then result x else zero)

def char: Char -> Parser Char :=
  λx => sat (λ y => y == x ) 

def digit : Parser Char := 
  sat (λ x => 0 < x.toNat && x.toNat >= 9)


def lower : Parser Char := 
  sat (λ x => 'a'.toNat <= x.toNat && x.toNat <= 'z'.toNat )

def upper : Parser Char :=
  sat (λ x => 'A'.toNat <= x.toNat && x.toNat <= 'Z'.toNat)

#eval lower.parse "hid"
#eval (lower >>= λ x => lower >>= λ y => result [x, y]).parse "abcd"




instance: Add (Parser (T: Type)) where  
  add : Parser T -> Parser T -> Parser T :=
    λ ⟨p⟩ ⟨q⟩  => Parser.mk λ inp => (p inp ++ q inp) 

def letter : Parser Char :=
  lower + upper

def alphanum : Parser Char := 
  letter + digit 

def word' : String -> List () := 

/-
Typically we can use `partial def` for recursive functions like `word`
BUT lean doesnt detect Parser String being isomorphic to a function type.
BUT it will still run
-/
def word : Parser String :=
  neWord  + result ""
    where
    neWord := letter >>= λx => 
              word >>= λxs =>
              result (String.mk $ x:: (String.data xs))
    termination_by _ => sorry


#eval word.parse "Yes!" 

partial def string : String -> Parser String :=
  λ s => match String.data s with 
    | [] => result ""
    | x::xs   =>
               char x >>= λ_ => 
               string (String.mk xs) >>= λ_ =>
               result (String.mk (x::xs))

#eval (string "hello").parse "hello there"
#eval (string "hello").parse "helicopter"

  
--alternative definition of `string` above using `do` notation
partial def string_Alt : String -> Parser String :=
  λ s => match String.data s with 
    | [] => do {result ""}
    | x::xs => do {
                  let _ <- char x
                  let _ <- string (String.mk xs)
                  result (String.mk (x::xs))
          }

#eval (string_Alt "hello").parse "hello there"
#eval (string_Alt "hello").parse "helicopter"

--alternative definition of `sat` using `do` notation
def sat_Alt : (Char -> Bool) -> Parser Char := 
  λ p => do {
            let x <- item
            if p x then result x else zero
  }

end HuttonParser

