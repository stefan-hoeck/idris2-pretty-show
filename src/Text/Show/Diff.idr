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

sameN : (indent: Nat) -> Name -> List DocDiff
sameN ind = same ind . unName

remAdd : (indent : Nat) -> Value -> Value -> List DocDiff
remAdd ind x y = removed ind (valToStr x) ++ added ind (valToStr y)

oneLine : Nat -> ValueDiff -> Lazy (List DocDiff) -> List DocDiff
oneLine ind v dds =
  let x = takeLeft v
      y = takeRight v
   in if oneLiner x && oneLiner y then remAdd ind x y else dds

mkDocDiff : (depth : Nat) -> (indent : Nat) -> ValueDiff -> List DocDiff
mkDocDiff _ ind (Same x)   = same ind (valToStr x)
mkDocDiff _ ind (Diff x y) = remAdd ind x y
mkDocDiff 0 _   _          = []

mkDocDiff (S k) ind v@(Con n xs) =
  oneLine ind v $ sameN ind n ++
                  concatMap (mkDocDiff k (ind + 2)) xs

mkDocDiff (S k) ind v@(Rec n xs) =
  oneLine ind v $ sameN ind n ++
                  [DocOpen ind "{"] ++
                  map (\(nm, x) => DocItem (ind + 2) ", " (sameN 0 (nm <+> " =") ++ mkDocDiff k 2 x)) xs ++
                  [DocClose ind "}"]

mkDocDiff (S k) ind v@(Tuple x y xs) =
  oneLine ind v $ [DocOpen ind "("] ++
                  map (DocItem ind ", " . mkDocDiff k 0) (x::y::xs) ++
                  [DocClose ind ")"]

mkDocDiff (S k) ind v@(Lst xs) =
  oneLine ind v $ [DocOpen ind "["] ++
                  map (DocItem ind ", " . mkDocDiff k 0) xs ++
                  [DocClose ind "]"]

spaces : Nat -> String
spaces ind = fastPack $ replicate ind ' '

mkLineDiff : (d : Nat) -> (ind : Nat) -> String -> DocDiff -> List LineDiff
-- mkLineDiff indent0 prefix0 diff =
--   let
--     mkLinePrefix indent =
--       spaces indent0 ++ prefix0 ++ spaces indent
-- 
--     mkLineIndent indent =
--       indent0 + length prefix0 + indent
--   in
--     case diff of
--       DocSame indent x ->
--         [LineSame $ mkLinePrefix indent ++ x]
-- 
--       DocRemoved indent x ->
--         [LineRemoved $ mkLinePrefix indent ++ x]
-- 
--       DocAdded indent x ->
--         [LineAdded $ mkLinePrefix indent ++ x]
-- 
--       DocOpen indent x ->
--         [LineSame $ mkLinePrefix indent ++ x]
-- 
--       DocItem _ _ [] ->
--         []
-- 
--       DocItem indent prefix (x@DocRemoved{} : y@DocAdded{} : xs) ->
--         mkLineDiff (mkLineIndent indent) prefix x ++
--         mkLineDiff (mkLineIndent indent) prefix y ++
--         concatMap (mkLineDiff (mkLineIndent (indent + length prefix)) "") xs
-- 
--       DocItem indent prefix (x : xs) ->
--         mkLineDiff (mkLineIndent indent) prefix x ++
--         concatMap (mkLineDiff (mkLineIndent (indent + length prefix)) "") xs
-- 
--       DocClose indent x ->
--         [LineSame $ spaces (mkLineIndent indent) ++ x]


collapseOpen : List DocDiff -> List DocDiff
collapseOpen (DocSame ind l :: DocOpen _ bra :: xs) =
  DocSame ind (l ++ " " ++ bra) :: collapseOpen xs
collapseOpen (DocItem ind pre xs :: ys) =
  DocItem ind pre (collapseOpen xs) :: collapseOpen ys
collapseOpen (x :: xs) = x :: collapseOpen xs
collapseOpen [] = []

dropLeadingSep : List DocDiff -> List DocDiff
dropLeadingSep (DocOpen oind bra :: DocItem ind pre xs :: ys) =
  DocOpen oind bra :: DocItem (ind + length pre) "" (dropLeadingSep xs) :: dropLeadingSep ys
dropLeadingSep (DocItem ind pre xs :: ys) =
  DocItem ind pre (dropLeadingSep xs) :: dropLeadingSep ys
dropLeadingSep (x :: xs) = x :: dropLeadingSep xs
dropLeadingSep [] = []

export
toLineDiff : ValueDiff -> List LineDiff
toLineDiff v =
  concatMap (\d => mkLineDiff (depth d) 0 "" d) .
  collapseOpen .
  dropLeadingSep $
  mkDocDiff (depth v) 0 v

export
lineDiff : Value -> Value -> List LineDiff
lineDiff x y = toLineDiff $ valueDiff x y

export
renderLineDiff : LineDiff -> String
renderLineDiff (LineSame x)    = "  " ++ x
renderLineDiff (LineRemoved x) = "- " ++ x
renderLineDiff (LineAdded x)   = "+ " ++ x

export
renderValueDiff : ValueDiff -> String
renderValueDiff = unlines . map renderLineDiff . toLineDiff
