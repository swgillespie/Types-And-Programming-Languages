import Data.List (delete);

-- The three fundamental forms of the untyped lambda calculus.
-- A "variable" is just a thing that can contain a value.
-- An "abstraction" is of the form λx.t, where t is a term.
-- An "application" is the invocation of a function.
data Term =
  Variable String
  | Abstraction String Term
  | Application Term Term
    deriving(Eq, Read)

instance Show Term where
  show (Variable s) = s
  show (Abstraction s t) = "λ" ++ s ++ "." ++ show t
  show (Application t1 t2) = show t1 ++ "(" ++ show t2 ++ ")"

-- A variable is said to be "free" if it is not bound by any enclosing abstraction.
freeVariables :: Term -> [String]
freeVariables (Variable s) = [s]
freeVariables (Abstraction s t) = delete s (freeVariables t)
freeVariables (Application t1 t2) = freeVariables t1 ++ freeVariables t2

-- A term is "closed" if it does not have any free variables.
isClosed :: Term -> Bool
isClosed t = null $ freeVariables t

-- Reduce performs one by-value reduction.
reduce :: Term -> Term
reduce (Application abs@(Abstraction _ _) t2) = bind abs t2
reduce (Application t1 t2) = Application (reduce t1) t2
reduce s = s

-- A term is "normal" (or "normalized") if it cannot be reduced any further.
isNormal :: Term -> Bool
isNormal t = t == reduce t

-- Bind substitutes a bound variable with a term, yielding a new term.
-- bind(s, t1, t2) = The term obtained by replacing all free occurances of x in t1
-- by t2.
bind :: Term -> Term -> Term
bind (Abstraction v t1) t2 = rec_bind v t1 t2 where
  rec_bind :: String -> Term -> Term -> Term
  rec_bind v (Variable p) t2 = if v == p then t2 else Variable p
  rec_bind v (Abstraction p t1) t2 = Abstraction p (rec_bind v t1 t2)
  rec_bind v (Application t1 t2) t3 = Application (rec_bind v t1 t3) (rec_bind v t2 t3)

-- The identity function is a function that maps its input to itself.
-- Written: λx.x
lambdaId :: Term
lambdaId = Abstraction "x" (Variable "x")

-- The true function represents a boolean true in the untyped lambda calculus.
true :: Term
true = Abstraction "t" (Abstraction "f" (Variable "t"))

-- Likewise, the false function represents a boolean false in the untyped lambda calculus.
false :: Term
false = Abstraction "t" (Abstraction "f" (Variable "f"))

doReduction :: Term -> IO ()
doReduction t = do
  if isNormal t then putStrLn ("Reduction complete: " ++ show t)
    else doReduction' (reduce t)

doReduction' :: Term -> IO ()
doReduction' t = do
  putStrLn ("Reduction: " ++ show t)
  doReduction t


-- Implementation of Church numerals
instance Enum Term where
  toEnum i = Abstraction "x" (toEnum (i - 1))
  toEnum 0 = Variable "x"
  
  fromEnum t = fromEnum' t 0 where
    fromEnum' :: Term -> Int -> Int
    fromEnum' (Variable _) i = i
    fromEnum' (Abstraction _ t) i = fromEnum t (i + 1)

instance Ord Term where
  compare t1 t2 = (fromEnum t1) `compare` (fromEnum t2)
