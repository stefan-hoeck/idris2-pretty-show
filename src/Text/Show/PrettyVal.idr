module Text.Show.PrettyVal

import Data.List
import Data.List1
import Data.Vect
import Text.Show.Value

||| A class for types that may be reified into a value.
||| Instances of this class may be derived automatically,
||| for datatypes that support `Generics`.
public export
interface PrettyVal a where
  constructor MkPrettyVal
  prettyVal : a -> Value

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
PrettyVal Void where
  prettyVal v impossible

public export
PrettyVal Value where
  prettyVal v = v

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

public export
PrettyVal Nat where
  prettyVal = Natural . show

mkNum :  (Ord a, Neg a, Num a, Show a)
      => (String -> Value) -> a -> Value
mkNum c x = if x >= 0 then c (show x)
                      else Neg . c . show $ negate x

public export
PrettyVal Int where
  prettyVal = mkNum Natural

public export
PrettyVal Int8 where
  prettyVal = mkNum Natural

public export
PrettyVal Int16 where
  prettyVal = mkNum Natural

public export
PrettyVal Int32 where
  prettyVal = mkNum Natural

public export
PrettyVal Int64 where
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
  prettyVal = Str . show

public export
PrettyVal a => PrettyVal (List a) where
  prettyVal = Lst . map prettyVal

public export
PrettyVal a => PrettyVal (Vect n a) where
  prettyVal = Lst . toList . map prettyVal

public export
(PrettyVal a, PrettyVal b) => PrettyVal (a,b) where
  prettyVal (a,b) = case prettyVal b of
    Tuple v1 v2 vs => Tuple (prettyVal a) v1 (v2 :: vs)
    val            => Tuple (prettyVal a) val []
