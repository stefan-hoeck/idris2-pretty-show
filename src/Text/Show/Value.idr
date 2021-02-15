module Text.Show.Value

import Data.List1
import Generics.Derive

%hide Language.Reflection.TT.Name

%language ElabReflection

%default total

||| A name.
public export
data Name = MkName String

%runElab derive "Text.Show.Value.Name" [Generic,Meta,Show,Eq,Ord]

public export
FromString Name where fromString = MkName

||| Generic Idris values.
||| The `String` in the literals is the text for the literals "as is".
||| 
||| A chain of infix constructors means that they appeared in the input string
||| without parentheses, i.e
||| 
||| `1 :+: 2 :*: 3` is represented with `InfixCons 1 [(":+:",2),(":*:",3)]`, whereas
||| 
||| `1 :+: (2 :*: 3)` is represented with `InfixCons 1 [(":+:",InfixCons 2 [(":*:",3)])]`.
public export
data Value = Con Name (List Value)
           | InfixCons Value (List (Name,Value))
           | Rec Name (List (Name,Value) )
           | Tuple (List Value)
           | Lst (List Value)
           | Neg Value
           | Natural String
           | Dbl String
           | Chr String
           | Str String

||| Hide constructors matching the given predicate.
||| If the hidden value is in a record, we also hide
||| the corresponding record field.
||| 
||| If the boolean flag is true, then we also hide
||| constructors all of whose fields were hidden.
public export
hideCon : Bool -> (Name -> Bool) -> Value -> Value
hideCon collapse hidden = toVal . delMaybe
  where
  hiddenV : Value
  hiddenV = Con "_" []

  toVal : Maybe Value -> Value
  toVal = fromMaybe hiddenV

  mutual
    delMany : (Functor f, Foldable f) => f Value -> Maybe (f Value)
    delMany vals =
      let newVals = map delMaybe vals
       in if collapse && all isNothing newVals
            then Nothing
            else Just (map toVal newVals)

    delMaybe : Value -> Maybe Value
    delMaybe val =
      case val of
           Con x vs =>
             if hidden x
               then Nothing
               else if null vs
                 then Just val
                 else Con x <$> delMany vs

           InfixCons v ys =>
             let (cs,vs) = unzip ys
                 mbs     = delay $ map delMaybe vs
              in if any hidden cs
                   then Nothing
                   else do (v1 ::: vs1) <- delMany (v ::: vs)
                           pure (InfixCons v1 (zip cs vs1))


           Rec x fs =>
             let (ls,vs) = delay $ unzip fs
                 mbs     = delay $ map delMaybe vs
              in if hidden x
                   then Nothing
                   else if null fs
                     then Just val
                     else if collapse && all isNothing mbs
                       then Nothing
                       else let ps = mapMaybe (\(f,mv) => (f,) <$> mv)
                                              (zip ls mbs)
                             in Just (Rec x ps)

           Tuple []  => Just val
           Tuple vs  => Tuple <$> delMany vs
           Lst []    => Just val
           Lst vs    => Lst <$> delMany vs
           Neg v     => Neg <$> delMaybe v
           Natural _ => Just val
           Dbl _     => Just val
           Chr _     => Just val
           Str _     => Just val

--------------------------------------------------------------------------------
--          Parsing
--------------------------------------------------------------------------------

export
parseValue : String -> Maybe Value
