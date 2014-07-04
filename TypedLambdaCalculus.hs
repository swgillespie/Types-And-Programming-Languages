import Prelude hiding (lookup);
import Data.Map (Map, insert, lookup, empty);

-- A term is either a variable, an abstraction (λx:T .x), an application,
-- or a boolean literal. We also add an "If" term for ease of expression.
-- It is very possible to express If in terms of the other terms.
data Term = Variable String
          | Abstraction (String, Type) Term
          | Application Term Term
          | BooleanLiteral Bool
          | If Term Term Term
            deriving(Eq, Show)

-- A type is either Boolean, or it is a function from one type to another type.
data Type = Boolean
          | Function Type Type
          | Error String
            deriving(Eq)

instance Show Type where
  show (Boolean) = "Bool"
  show (Function t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (Error s) = "Error: " ++ s
  
type Environment = Map String Type

-- Typecheck ensures that our lambda calculus program obeys the following rules:
-- 1. In an "if" term, the condition term must have type Boolean, and the two branch terms
--    must have the same type.
-- 2. In a variable term, the variable must not be free.
-- 3. In an application term, if the first term has type T1 -> T2, the second term must have type
--    T1.
-- 4. In an application term, the first term must be a function.
typecheck :: Environment -> Term -> Type
typecheck e (Abstraction (s, t) t1) = Function t (typecheck (insert s t e) t1)
typecheck e (Variable s) = case lookup s e of
  Just t -> t
  Nothing -> Error $ "Unbound variable: " ++ show s
typecheck e (Application t1 t2) = case (typedt1, typedt2) of
  ((Function tt1 tt2), tt3) -> if tt1 == tt3 then tt2 else Error $ "Incompatable types: " ++ show tt1 ++ ", " ++ show tt2
  (t, _) -> Error $ "Term one of application is not a function: " ++ show t
  where
    typedt1 = typecheck e t1
    typedt2 = typecheck e t2
typecheck e (BooleanLiteral b) = Boolean
typecheck e (If cond tru fls) = if condType /= Boolean then Error $ "Condition must be boolean, got: " ++ show condType else checkBranches e tru fls
  where
    condType = typecheck e cond
    checkBranches :: Environment -> Term -> Term -> Type
    checkBranches e t f = if typet == typef then typet else Error $ "Branches have heterogenous types: " ++ show typet ++ ", " ++ show typef
      where
        typet = typecheck e t
        typef = typecheck e f

-- Reduce performs one by-value reduction.
reduce :: Term -> Term
reduce (Application abs@(Abstraction _ _) t2) = bind abs t2
reduce (Application t1 t2) = Application (reduce t1) t2
reduce (If (BooleanLiteral True) t1 t2) = t1
reduce (If (BooleanLiteral False) t1 t2) = t2
reduce (If cond t1 t2) = If (reduce cond) t1 t2
reduce s = s

-- A term is "normal" (or "normalized") if it cannot be reduced any further.
isNormal :: Term -> Bool
isNormal t = t == reduce t

-- Bind substitutes a bound variable with a term, yielding a new term.
-- bind(s, t1, t2) = The term obtained by replacing all free occurances of x in t1
-- by t2.
bind :: Term -> Term -> Term
bind (Abstraction (v, _) t1) t2 = rec_bind v t1 t2 where
  rec_bind :: String -> Term -> Term -> Term
  rec_bind v (Variable p) t2 = if v == p then t2 else Variable p
  rec_bind v (Abstraction (p, s) t1) t2 = Abstraction (p, s) (rec_bind v t1 t2)
  rec_bind v (Application t1 t2) t3 = Application (rec_bind v t1 t3) (rec_bind v t2 t3)
  rec_bind v (If cond t1 t2) t3 = If (rec_bind v cond t3) (rec_bind v t1 t3) (rec_bind v t2 t3)

-- doEvaluate type checks the input and then does a reduction if it is correct.
doEvaluate :: Term -> IO ()
doEvaluate t = case typecheck empty t of
  Error s -> putStrLn ("Failed to typecheck: " ++ s)
  o -> doReduction t

doReduction :: Term -> IO ()
doReduction t = do
  if isNormal t then putStrLn ("Reduction complete: " ++ show t)
    else doReduction' t

doReduction' :: Term -> IO ()
doReduction' t = do
  putStrLn ("Reduction: " ++ show t)
  doReduction (reduce t)
