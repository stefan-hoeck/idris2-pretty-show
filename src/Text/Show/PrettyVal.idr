module Text.Show.PrettyVal

import Data.List
import Data.Vect
import Text.Show.Value

import Generics.Derive

%hide Language.Reflection.TT.Name

||| A class for types that may be reified into a value.
||| Instances of this class may be derived automatically,
||| for datatypes that support `Generics`.
public export
interface PrettyVal a where
  prettyVal : a -> Value

--------------------------------------------------------------------------------
--          Generics
--------------------------------------------------------------------------------

-- displays an applied binary operator
-- if the same operator appears severak timtes in a row,
-- this is treated as a list of infix constructors.
binOp : (prf : NP (PrettyVal . f) [a,b]) => Name -> NP f [a,b] -> Value
binOp op vs =
  let [pvx,pvy] = hcmap (PrettyVal . f) prettyVal vs
   in case pvy of
           InfixCons pv1 pairs@((op2, pv2) :: xs) =>
             if op2 == op then InfixCons pvx ((op,pvy) :: pairs)
                          else InfixCons pvx [(op,pvy)]
           _ => InfixCons pvx [(op,pvy)]

rec : NP (PrettyVal . f) ks => Name -> NP f ks -> NP (K String) ks -> Value
rec con args names =
  let applied = hcliftA2 (PrettyVal . f) named names args
   in Rec con (collapseNP applied)

  where named : PrettyVal a => String -> a -> (Name,Value)
        named name v = (MkName name,prettyVal v)

other : NP (PrettyVal . f) ks => Name -> NP f ks -> Value
other con args =
  let argLst = collapseNP $ hcmap (PrettyVal . f) prettyVal args
   in Con con argLst

-- Displays a single applied constructor
valC : (prf : NP (PrettyVal . f) ks) => ConInfo ks -> NP f ks -> Value
valC info args =
  let con   = MkName (wrapOperator info.conName)
      names = argNames info
      val   = maybe (other con args) (rec con args) names
   in case args of
        []    => Con con []
        [a,b] => if isOperator info.conName
                    then binOp {prf} (MkName info.conName) [a,b]
                    else val
        _     => val

-- ||| Generic show function.
-- |||
-- ||| This is still quite basic. It uses prefix notation for operators
-- ||| and data types with List constructors (`Nil` and `(::)`)
-- ||| are not yet displayed using list syntax ("[a,b,c]").
-- |||
-- ||| However, constructors with only named arguments are displayed
-- ||| in record syntax style.
-- public export
-- genShowPrec : Meta t code => POP Show code => Prec -> t -> String
-- genShowPrec p = showSOP p (metaFor t) . from

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
PrettyVal () where
  prettyVal _ = Con "()" []

public export
PrettyVal Bits8 where
  prettyVal = Natural . show

public export
PrettyVal Bits16 where
  prettyVal = Natural . show

public export
PrettyVal Bits32 where
  prettyVal = Natural . show

public export
PrettyVal Bits64 where
  prettyVal = Natural . show

mkNum :  (Ord a, Neg a, Num a, Show a)
      => (String -> Value) -> a -> Value
mkNum c x = if x >= 0 then c (show x)
                      else Neg . c . show $ negate x

public export
PrettyVal Int where
  prettyVal = mkNum Natural

public export
PrettyVal Integer where
  prettyVal = mkNum Natural

public export
PrettyVal Double where
  prettyVal = mkNum Dbl

public export
PrettyVal Char where
  prettyVal = Chr . show

public export
PrettyVal String where
  prettyVal = Str

public export
PrettyVal a => PrettyVal (List a) where
  prettyVal = Lst . map prettyVal

public export
PrettyVal a => PrettyVal (Vect n a) where
  prettyVal = Lst . toList . map prettyVal

public export
(PrettyVal a, PrettyVal b) => PrettyVal (a,b) where
  prettyVal (a,b) = case prettyVal b of
                         Tuple vs => Tuple (prettyVal a :: vs)
                         val      => Tuple [prettyVal a, val]

public export
NP (PrettyVal . f) ks => PrettyVal (NP_ k f ks) where
  prettyVal np = Lst . collapseNP $ hcmap (PrettyVal . f) prettyVal np

public export
NP (PrettyVal . f) ks => PrettyVal (NS_ k f ks) where
  prettyVal ns = run $ hcmap (PrettyVal . f) prettyVal ns
    where run : NS_ k (K Value) xs -> Value
          run (Z v) = Con "Z" [v]
          run (S x) = Con "S" [run x]

public export
POP (PrettyVal . f) kss => PrettyVal (POP_ k f kss) where
  prettyVal (MkPOP nps) = Con "MkPOP" [prettyVal nps]

public export
POP (PrettyVal . f) kss => PrettyVal (SOP_ k f kss) where
  prettyVal (MkSOP nss) = Con "MkSOP" [prettyVal nss]

-- oneVal :: [(Name,Value)] -> Value
-- oneVal x =
--   case x of
--     [ ("",v) ]               -> v
--     fs | all (null . fst) fs -> Con "?" (map snd fs)
--        | otherwise           -> Rec "?" fs
-- 
-- 
-- instance PrettyVal Bool
-- instance PrettyVal Ordering
-- instance PrettyVal a => PrettyVal (Maybe a)
-- instance (PrettyVal a, PrettyVal b) => PrettyVal (Either a b)
-- 
-- instance PrettyVal Text where
--   prettyVal = String . Text.unpack
