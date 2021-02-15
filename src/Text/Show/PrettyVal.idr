module Text.Show.PrettyVal

import Data.List
import Data.Vect
import Text.Show.Value

import Generics.Derive

%hide Language.Reflection.TT.Name

%language ElabReflection

%default total


||| A class for types that may be reified into a value.
||| Instances of this class may be derived automatically,
||| for datatypes that support `Generics`.
public export
interface PrettyVal a where
  prettyVal : a -> Value

--------------------------------------------------------------------------------
--          Generics
--------------------------------------------------------------------------------

-- Displays an applied constructer in record syntax.
-- This is called, if all arguments have user-defined names.
rec : Name -> NP (K Value) ks -> NP (K String) ks -> Value
rec con vs ns = Rec con (collapseNP $ hliftA2 named vs ns)
  where named : Value -> String -> (Name,Value)
        named v name = (MkName name, v)

-- Displays an applied constructer with unnamed arguments.
other : Name -> NP (K Value) ks -> Value
other con = Con con . collapseNP

-- Displays a single applied constructor
valC : NP (PrettyVal . f) ks => ConInfo ks -> NP f ks -> Value
valC info args =
  let con   = MkName (wrapOperator info.conName)
      names = argNames info
      vals  = hcmap (PrettyVal . f) prettyVal args
      val   = maybe (other con vals) (rec con vals) names
   in case vals of
        []    => Con con []
        [a,b] => if isOperator info.conName
                    then binOp (MkName info.conName) a b
                    else val
        _     => val

prettySOP :  (all : POP (PrettyVal . f) kss)
          => TypeInfo kss -> SOP f kss -> Value
prettySOP {all = MkPOP _} (MkTypeInfo _ _ cons) =
  collapseNS . hcliftA2 (NP $ PrettyVal . f) valC cons . unSOP

||| Generic version of `prettyVal`.
public export
genPrettyVal : Meta t code => POP PrettyVal code => t -> Value
genPrettyVal = prettySOP (metaFor t) . from

--------------------------------------------------------------------------------
--          Auto Deriving
--------------------------------------------------------------------------------

namespace Derive

  ||| Creates a `Show` value from the passed functions.
  public export %inline
  mkPrettyVal : (prettyVal : a -> Value) -> PrettyVal a
  mkPrettyVal = %runElab check (var $ singleCon "PrettyVal")

  ||| Derives a `PrettyVal` implementation for the given data type
  ||| and visibility.
  export
  PrettyValVis : Visibility -> DeriveUtil -> InterfaceImpl
  PrettyValVis vis g = MkInterfaceImpl "PrettyVal" vis []
                         `(mkPrettyVal genPrettyVal)
                         (implementationType `(PrettyVal) g)

  ||| Alias for `PrettyValVis Public`.
  export
  PrettyVal : DeriveUtil -> InterfaceImpl
  PrettyVal = PrettyValVis Public

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
