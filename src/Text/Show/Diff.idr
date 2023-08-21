module Text.Show.Diff

import Data.Vect
import Derive.Prelude
import public Text.Show.Pretty

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Diff Data Types
--------------------------------------------------------------------------------

public export
data ValueDiff : Type where
  Con    : VName -> List ValueDiff -> ValueDiff
  Rec    : VName -> List (VName, ValueDiff) -> ValueDiff
  Tuple  : ValueDiff -> ValueDiff -> List ValueDiff -> ValueDiff
  Lst    : List ValueDiff -> ValueDiff
  Same   : Value -> ValueDiff
  Diff   : Value -> Value -> ValueDiff

%runElab derive "ValueDiff" [Show,Eq,PrettyVal]

public export
data LineDiff : Type where
  LineSame    : String -> LineDiff
  LineRemoved : String -> LineDiff
  LineAdded   : String -> LineDiff

%runElab derive "LineDiff" [Show,Eq,PrettyVal]

public export
data DocDiff : Type where
  DocSame    : Nat -> String -> DocDiff
  DocRemoved : Nat -> String -> DocDiff
  DocAdded   : Nat -> String -> DocDiff
  DocOpen    : Nat -> String -> DocDiff
  DocItem    : Nat -> String -> List DocDiff -> DocDiff
  DocClose   : Nat -> String -> DocDiff

%runElab derive "DocDiff" [Show,Eq,PrettyVal]

--------------------------------------------------------------------------------
--          Diffing
--------------------------------------------------------------------------------

export
valueDiff : Value -> Value -> ValueDiff

zipDiff :
     SnocList ValueDiff
  -> List Value
  -> List Value
  -> Maybe (List ValueDiff)
zipDiff sx [] [] = Just $ sx <>> []
zipDiff sx (x :: xs) (y :: ys) = zipDiff (sx :< valueDiff x y) xs ys
zipDiff _ _ _ = Nothing

zipDiffP :
     SnocList (VName, ValueDiff)
  -> List (VName, Value)
  -> List (VName, Value)
  -> Maybe (List (VName, ValueDiff))
zipDiffP sx [] [] = Just $ sx <>> []
zipDiffP sx ((n1,x) :: xs) ((n2,y) :: ys) =
  if n1 == n2 then zipDiffP (sx :< (n1, valueDiff x y)) xs ys else Nothing
zipDiffP _ _ _ = Nothing

valueDiff x@(Con nx xs) y@(Con ny ys) =
    if nx == ny
       then maybe (Diff x y) (Con ny) (zipDiff [<] xs ys)
       else Diff x y
valueDiff x@(Rec nx xs) y@(Rec ny ys) =
    if nx == ny
       then maybe (Diff x y) (Rec ny) (zipDiffP [<] xs ys)
       else Diff x y
valueDiff x@(Lst xs) y@(Lst ys) = maybe (Diff x y) Lst (zipDiff [<] xs ys)
valueDiff x@(Tuple x1 x2 xs) y@(Tuple y1 y2 ys) = case zipDiff [<] xs ys of
  Nothing => Diff x y
  Just ds => Tuple (valueDiff x1 y1) (valueDiff x2 y2) ds
valueDiff x y = if x == y then Same x else Diff x y

take : (f : Value -> Value -> Value) -> ValueDiff -> Value
take f v = case v of
  Con x xs     => Con x $ ts xs
  Rec x xs     => Rec x $ tsP xs
  Tuple x y xs => Tuple (take f x) (take f y) (ts xs)
  Lst xs       => Lst $ ts xs
  Same x       => x
  Diff x y     => f x y

  where
    ts : List ValueDiff -> List Value
    ts []       = []
    ts (h :: t) = take f h :: ts t

    tsP : List (a,ValueDiff) -> List (a,Value)
    tsP []           = []
    tsP ((a,h) :: t) = (a,take f h) :: tsP t

export
takeLeft : ValueDiff -> Value
takeLeft = take $ \x,_ => x

export
takeRight : ValueDiff -> Value
takeRight = take $ \_,y => y

oneLiner : Value -> Bool
oneLiner x =
  case lines (valToStr x) of
     _ :: Nil   => True
     _          => False

removed : (indent: Nat) -> String -> List DocDiff
removed ind = map (DocRemoved ind) . lines

added : (indent: Nat) -> String -> List DocDiff
added ind = map (DocAdded ind) . lines

same : (indent: Nat) -> String -> List DocDiff
same ind = map (DocSame ind) . lines

sameN : (indent: Nat) -> VName -> SnocList DocDiff
sameN ind = ([<] <><) . same ind . unName

remAdd : (indent : Nat) -> Value -> Value -> List DocDiff
remAdd ind x y = removed ind (valToStr x) ++ added ind (valToStr y)

oneLine : Nat -> ValueDiff -> Lazy (List DocDiff) -> List DocDiff
oneLine ind v dds =
  let x = takeLeft v
      y = takeRight v
   in if oneLiner x && oneLiner y then remAdd ind x y else dds

docDiff : (indent : Nat) -> ValueDiff -> List DocDiff

docDiffs :
      SnocList DocDiff
   ->(indent : Nat)
   -> List ValueDiff
   -> List DocDiff
docDiffs sx ind (x :: xs) = docDiffs (sx <>< docDiff ind x) ind xs
docDiffs sx ind []        = sx <>> []

docItems :
      SnocList DocDiff
   ->(indent : Nat)
   -> List ValueDiff
   -> SnocList DocDiff
docItems sx ind (x :: xs) =
  docItems (sx :< DocItem ind ", " (docDiff 0 x)) ind xs
docItems sx ind []        = sx

docPairs :
      SnocList DocDiff
   ->(indent : Nat)
   -> List (VName,ValueDiff)
   -> SnocList DocDiff
docPairs sx ind ((n,x) :: xs) =
  let ds := sameN 0 (n <+> " =") <>> docDiff 2 x
   in docPairs (sx :< DocItem ind ", " ds) ind xs
docPairs sx ind []        = sx

docDiff ind (Same x)   = same ind (valToStr x)
docDiff ind (Diff x y) = remAdd ind x y
docDiff ind v@(Con n xs) =
  oneLine ind v $ docDiffs (sameN ind n) (ind + 2) xs
docDiff ind v@(Lst xs) =
  oneLine ind v $ DocOpen ind "[" :: (docItems [<] ind xs <>> [DocClose ind "]"])
docDiff ind v@(Tuple x y xs) =
  oneLine ind v $
    DocOpen ind "(" ::
    DocItem ind ", " (docDiff 0 x) ::
    DocItem ind ", " (docDiff 0 y) ::
    (docItems [<] ind xs <>> [DocClose ind ")"])
docDiff ind v@(Rec n xs) =
  oneLine ind v $
    sameN ind n <>>
    DocOpen ind "{" ::
    (docPairs [<] (ind + 2) xs <>> [DocClose ind "}"])

spaces : Nat -> String
spaces ind = fastPack $ replicate ind ' '

mkLineDiff : (ind : Nat) -> String -> DocDiff -> List LineDiff

mkLineDiffs :
     SnocList LineDiff
  -> (ind : Nat)
  -> List DocDiff
  -> List LineDiff
mkLineDiffs sx ind (x :: xs) =
  mkLineDiffs (sx <>< mkLineDiff ind "" x) ind xs
mkLineDiffs sx ind []        = sx <>> []

mkLineDiff ind0 pre0 diff =
  case diff of
    DocSame i x    => [LineSame $ mkLinePrefix i ++ x]
    DocRemoved i x => [LineRemoved $ mkLinePrefix i ++ x]
    DocAdded i x   => [LineAdded $ mkLinePrefix i ++ x]
    DocOpen i x    => [LineSame $ mkLinePrefix i ++ x]
    DocClose i x   => [LineSame $ spaces (mkLineIndent i) ++ x]
    DocItem _ _ [] => []
    DocItem i p (x@(DocRemoved _ _) :: y@(DocAdded _ _) :: xs) =>
      mkLineDiff (mkLineIndent i) p x ++
      mkLineDiff (mkLineIndent i) p y ++
      mkLineDiffs [<] (mkLineIndent (i + length p)) xs

    DocItem i p (x :: xs) =>
      mkLineDiff (mkLineIndent i) p x ++
      mkLineDiffs [<] (mkLineIndent (i + length p)) xs

  where mkLinePrefix : Nat -> String
        mkLinePrefix ind = spaces ind0 ++ pre0 ++ spaces ind

        mkLineIndent : Nat -> Nat
        mkLineIndent ind = ind0 + length pre0 + ind

collapseOpen : List DocDiff -> List DocDiff
collapseOpen (DocSame ind l :: DocOpen _ bra :: xs) =
  DocSame ind (l ++ " " ++ bra) :: collapseOpen xs
collapseOpen (DocItem ind pre xs :: ys) =
  DocItem ind pre (collapseOpen xs) :: collapseOpen ys
collapseOpen (x :: xs) = x :: collapseOpen xs
collapseOpen [] = []

dropLeadingSep : List DocDiff -> List DocDiff
dropLeadingSep (DocOpen oind bra :: DocItem ind pre xs :: ys) =
     DocOpen oind bra
  :: DocItem (ind + length pre) "" (dropLeadingSep xs)
  :: dropLeadingSep ys
dropLeadingSep (DocItem ind pre xs :: ys) =
  DocItem ind pre (dropLeadingSep xs) :: dropLeadingSep ys
dropLeadingSep (x :: xs) = x :: dropLeadingSep xs
dropLeadingSep [] = []

export
toLineDiff : ValueDiff -> List LineDiff
toLineDiff v =
  concatMap (mkLineDiff 0 "") .
  collapseOpen .
  dropLeadingSep $
  docDiff 0 v

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
