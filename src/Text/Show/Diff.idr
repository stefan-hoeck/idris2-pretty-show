module Text.Show.Diff

import Data.Vect
import Generics.Derive
import public Text.Show.Pretty

%hide Language.Reflection.TT.Name

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Diff Data Types
--------------------------------------------------------------------------------

public export
data ValueDiff = Con Name (List ValueDiff)
               | Rec Name (List (Name, ValueDiff))
               | Tuple ValueDiff ValueDiff (List ValueDiff)
               | Lst (List ValueDiff)
               | Same Value
               | Diff Value Value

%runElab derive "ValueDiff" [Generic,Meta]

export covering
Eq ValueDiff where (==) = genEq

export covering
Show ValueDiff where showPrec = genShowPrec

namespace ValueDiff
  export
  depth : ValueDiff -> Nat
  depth v = case v of
                 (Con x xs)     => S $ maxDepth xs
                 (Rec x xs)     => S $ maxDepthP xs
                 (Tuple x y xs) => S . max (depth x) $ max (depth y) (maxDepth xs)
                 (Lst xs)       => S $ maxDepth xs
                 (Same x)       => 0
                 (Diff x y)     => 0
  
    where maxDepth : List ValueDiff -> Nat
          maxDepth []       = 0
          maxDepth (h :: t) = max (depth h) (maxDepth t)

          maxDepthP : List (a,ValueDiff) -> Nat
          maxDepthP []           = 0
          maxDepthP ((_,h) :: t) = max (depth h) (maxDepthP t)

public export
data LineDiff = LineSame String
              | LineRemoved String
              | LineAdded String

%runElab derive "LineDiff" [Generic,Meta,Show,Eq]

public export
data DocDiff = DocSame Nat String
             | DocRemoved Nat String
             | DocAdded Nat String
             | DocOpen Nat String
             | DocItem Nat String (List DocDiff)
             | DocClose Nat String

%runElab derive "DocDiff" [Generic,Meta]

export covering
Eq DocDiff where (==) = genEq

export covering
Show DocDiff where showPrec = genShowPrec

namespace DocDiff
  export
  depth : DocDiff -> Nat
  depth v = case v of
                 DocItem _ _ ds => S $ maxDepth ds
                 _              => 0
  
    where maxDepth : List DocDiff -> Nat
          maxDepth []       = 0
          maxDepth (h :: t) = max (depth h) (maxDepth t)

--------------------------------------------------------------------------------
--          Diffing
--------------------------------------------------------------------------------

-- using the sledgehammer of totality here, since I couldn't satisfy
-- the totality checker otherwise.
valueDiffN : (depth : Nat) -> Value -> Value -> ValueDiff
valueDiffN 0 x y = if x == y then Same x else Diff x y
valueDiffN (S k) x y =
  case (x, y) of
       (Con nx xs, Con ny ys) =>
         if nx == ny  && length xs == length ys
            then Con nx (zipWith (valueDiffN k) xs ys)
            else Diff x y

       (Lst xs, Lst ys) =>
         if length xs == length ys
            then Lst (zipWith (valueDiffN k) xs ys)
            else Diff x y

       (Tuple v1 v2 vs, Tuple w1 w2 ws) =>
         if length vs == length ws
            then Tuple (valueDiffN k v1 w1)
                       (valueDiffN k v2 w2)
                       (zipWith (valueDiffN k) vs ws)
            else Diff x y

       (Rec nx nxs, Rec ny nys) =>
         let ns = map fst nxs
          in if nx == ny && ns == map fst nys
                then Rec nx . zip ns $ zipWith (valueDiffN k)
                                               (map snd nxs)
                                               (map snd nys)
                else Diff x y

       _ => if x == y then Same x else Diff x y

export
valueDiff : Value -> Value -> ValueDiff
valueDiff v w = valueDiffN (depth v `max` depth w) v w

take : (f : Value -> Value -> Value) -> ValueDiff -> Value
take f v = case v of
             Con x xs     => Con x $ ts xs
             Rec x xs     => Rec x $ tsP xs
             Tuple x y xs => Tuple (take f x) (take f y) (ts xs)
             Lst xs       => Lst $ ts xs
             Same x       => x
             Diff x y     => f x y

  where ts : List ValueDiff -> List Value
        ts []       = []
        ts (h :: t) = take f h :: ts t

        tsP : List (a,ValueDiff) -> List (a,Value)
        tsP []           = []
        tsP ((a,h) :: t) = (a,take f h) :: tsP t

export
takeLeft : ValueDiff -> Value
takeLeft = take \x,_ => x

export
takeRight : ValueDiff -> Value
takeRight = take \_,y => y

oneLiner : Value -> Bool
oneLiner x = case lines (valToStr x) of
               _ :: _ :: _ => False
               _           => True

removed : (indent: Nat) -> String -> List DocDiff
removed ind = map (DocRemoved ind) . lines

added : (indent: Nat) -> String -> List DocDiff
added ind = map (DocAdded ind) . lines

same : (indent: Nat) -> String -> List DocDiff
same ind = map (DocSame ind) . lines

mkDocDiffN : (depth : Nat) -> (indent : Nat) -> ValueDiff -> List DocDiff
mkDocDiffN _ ind (Same x)   = same ind (valToStr x)
mkDocDiffN _ ind (Diff x y) = removed ind (valToStr x) ++ added ind (valToStr y)
mkDocDiffN 0 _   _          = []
mkDocDiffN (S k) ind v =
  let x  = takeLeft v
      y  = takeRight v
   in if oneLiner x && oneLiner y
         then removed ind (valToStr x) ++ added ind (valToStr y)
         else ?foo
--  ValueCon n xs ->
--    same ind n ++
--    concatMap (mkDocDiff (ind + 2)) xs
--
--  ValueRec n nxs ->
--    same ind n ++
--    [DocOpen ind "{"] ++
--    fmap (\(name, x) -> DocItem (ind + 2) ", " (same 0 (name ++ " =") ++ mkDocDiff 2 x)) nxs ++
--    [DocClose (ind + 2) "}"]
--
--  ValueTuple xs ->
--    [DocOpen ind "("] ++
--    fmap (DocItem ind ", " . mkDocDiff 0) xs ++
--    [DocClose ind ")"]
--
--  ValueList xs ->
--    [DocOpen ind "["] ++
--    fmap (DocItem ind ", " . mkDocDiff 0) xs ++
--    [DocClose ind "]"]
--
--  ValueDiff x y ->
--    removed ind (valToStr x) ++
--    added ind (valToStr y)

-- 
-- 
