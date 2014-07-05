import Prelude hiding (lookup);
import Data.Map (Map, insert, lookup, empty)

data Term = BooleanLiteral Bool
          | NaturalLiteral Integer
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Variable String
          | Abstraction (String, Type) Term
          | Application Term Term
            deriving(Eq, Show)

data Type = Boolean
          | Natural
          | Function Type Type
          | Error String
            deriving(Eq)

instance Show Type where
  show (Boolean) = "Bool"
  show (Natural) = "Nat"
  show (Function t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (Error s) = "Error: " ++ s

type Environment = Map String Type

typeof :: Environment -> Term -> Type
typeof e (BooleanLiteral _) = Boolean
typeof e (NaturalLiteral _) = Natural
typeof e (Zero) = Natural
typeof e (Succ t) = if ttype == Natural then Natural
                    else Error $ "Succ expected type Nat, got " ++ show ttype
                         where
                           ttype = typeof e t
typeof e (Pred Zero) = Error $ "Pred of Zero is undefined"
typeof e (Pred t) = if ttype == Natural then Natural
                    else Error $ "Pred expected type Nat, got " ++ show ttype
                         where
                           ttype = typeof e t
typeof e (IsZero t) = if ttype == Natural then Boolean
                      else Error $ "IsZero expected type Nat, got " ++ show ttype
                           where
                             ttype = typeof e t
typeof e (Variable s) = case lookup s e of
  Just t -> t
  Nothing -> Error $ "Unbound variable: " ++ show s
typeof e (Abstraction (s, t) t1) = Function t (typeof (insert s t e) t1)
typeof e (Application t1 t2) = case (typedt1, typedt2) of
  ((Function tt1 tt2), tt3) -> if tt1 == tt3 then tt2
                               else Error $ "Incompatable types: " ++ show tt1 ++ ", " ++ show tt3
  (t, _) -> Error $ "Term one of application is not a function: " ++ show t
  where
    typedt1 = typeof e t1
    typedt2 = typeof e t2
typeof e (If cond tru fls) = if condType == Boolean then armTypes e tru fls
                             else Error $ "Condition must be Bool, got: " ++ show condType
  where
    condType = typeof e cond
    armTypes :: Environment -> Term -> Term -> Type
    armTypes e t f = if typet == typef then typet
                     else Error $ "Branches have heterogenous types: "
                          ++ show typet ++ ", " ++ show typef
      where
        typet = typeof e t
        typef = typeof e f

-- Reduce performs one by-value reduction.
reduce :: Term -> Term
reduce (Application abs@(Abstraction _ _) t2) = bind abs t2
reduce (Application t1 t2) = Application (reduce t1) t2
reduce (If (BooleanLiteral True) t1 t2) = t1
reduce (If (BooleanLiteral False) t1 t2) = t2
reduce (If cond t1 t2) = If (reduce cond) t1 t2
reduce (Succ (NaturalLiteral i)) = NaturalLiteral (i + 1)
reduce (Succ Zero) = NaturalLiteral 1
reduce (Succ t) = Succ (reduce t)
reduce (Pred (NaturalLiteral 1)) = Zero
reduce (Pred (NaturalLiteral i)) = NaturalLiteral (i - 1)
reduce (Pred t) = Pred (reduce t)
reduce (IsZero Zero) = BooleanLiteral True
reduce (IsZero (NaturalLiteral _)) = BooleanLiteral False
reduce (IsZero t) = IsZero (reduce t)
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
  rec_bind v (Succ t) t3 = Succ (rec_bind v t t3)
  rec_bind v (Pred t) t3 = Pred (rec_bind v t t3)
  rec_bind v (IsZero t ) t3 = IsZero (rec_bind v t t3)
  rec_bind v t1 t2 = t1

applyWhile :: (a -> Bool) -> (a -> a) -> a -> a
applyWhile c f t = if c t then applyWhile c f (f t) else t

-- Fully reduce will attempt to reduce a term until it is normalized,
-- after which it will stop.
-- Question: does this function always terminate?
-- (I'll have the proof soon hehe)
fullyReduce :: Term -> Term
fullyReduce = applyWhile (not . isNormal) reduce
