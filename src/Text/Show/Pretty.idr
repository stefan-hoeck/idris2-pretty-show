module Text.Show.Pretty

import Data.List
import Text.PrettyPrint.Prettyprinter

import public Text.Show.Value
import public Text.Show.PrettyVal

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- Don't put parenthesis around constructors in infix chains
isInfixAtom : Value -> Bool
isInfixAtom (InfixCons _ _) = False
isInfixAtom (Neg _)         = False
isInfixAtom _               = True

isAtom : Value -> Bool
isAtom (Con _ (_ :: _))  = False
isAtom v                 = isInfixAtom v

blockWith :  (List (Doc ann) -> Doc ann)
          -> Char
          -> Char
          -> List (Doc ann) -> Doc ann
blockWith _ a b []       = pretty a <+> pretty b
blockWith f a b (d::ds)  = f $  (pretty a <++> d)
                             :: [ pretty ',' <++> x | x <- ds ]
                             ++ [ pretty b ]

block : Char -> Char -> List (Doc ann) -> Doc ann
block = blockWith sep

hangAfter : Doc ann -> Int -> Doc ann -> Doc ann
hangAfter pre n po = sep [pre, nest n po]

toDoc : Value -> Doc ann
toDoc val =
  case val of
    Con (MkName "") vs => sep $ atoms vs
    Con (MkName c)  [] => pretty c
    Con (MkName c)  vs => hangAfter (pretty c) 2 (sep $ atoms vs)
    InfixCons v1 cvs   => hangsep (infx v1 cvs)
    Rec c fs           => hangAfter (pretty c) 2 $ block '{' '}' (fields fs)
    Lst vs             => block '[' ']' (docs vs)
    Tuple v1 v2 vs     => block '(' ')' (toDoc v1 :: toDoc v2 :: docs vs)
    Neg v              => pretty '-' <+> atom v
    Natural x          => pretty x
    Dbl x              => pretty x
    Chr x              => pretty x
    Str x              => pretty x
    _                  => neutral

  where
    atom : Value -> Doc ann
    atom v = if isAtom v then toDoc v else parens (toDoc v)

    -- the explicit list mappings like `atoms`, `docs`, and
    -- `fields` are necessary to convince the totality checker.
    atoms : List Value -> List (Doc ann)
    atoms []        = []
    atoms (x :: xs) = atom x :: atoms xs

    infixAtom : Value -> Doc ann
    infixAtom v = if isInfixAtom v then toDoc v else parens (toDoc v)

    field : (Name,Value) -> Doc ann
    field (x,v) = hangAfter (pretty x <++> pretty '=') 2 (toDoc v)

    fields : List (Name,Value) -> List (Doc ann)
    fields []        = []
    fields (p :: ps) = field p :: fields ps

    docs : List Value -> List (Doc ann)
    docs []        = []
    docs (x :: xs) = toDoc x :: docs xs

    infx : Value -> List (Name,Value) -> List (Doc ann)
    infx v []             = [infixAtom v]
    infx v ((n,v2)::cvs') = (infixAtom v <++> pretty n) :: infx v2 cvs'

    hangsep : List (Doc ann) -> Doc ann
    hangsep []      = neutral
    hangsep (x::xs) = hangAfter x 2 (sep xs)

||| Pretty print a generic value. Our intention is that the result is
||| equivalent to the 'Show' instance for the original value, except possibly
||| easier to understand by a human.
export
valToDoc : Value -> Doc ann
valToDoc = toDoc

||| Pretty print a generic value. Our intention is that the result is
||| equivalent to the 'Show' instance for the original value, except possibly
||| easier to understand by a human.
export
valToStr : Value -> String
valToStr = show . valToDoc {ann = ()}

--------------------------------------------------------------------------------
--          Pretty via Show
--------------------------------------------------------------------------------

export covering
reify : Show a => a -> Maybe Value
reify = parseValue . show

||| Try to show a value, prettily. If we do not understand the value, then we
||| just use its standard 'Show' instance.
export covering
ppDoc : Show a => a -> Doc ann
ppDoc a = let txt = show a
           in maybe (fromString txt) valToDoc (parseValue txt)

||| Convert a generic value into a pretty 'String', if possible.
export covering
ppShow : Show a => a -> String
ppShow = show . ppDoc {ann = ()}

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export covering
ppDocList : (Foldable f, Show a) => f a -> Doc ann
ppDocList = blockWith vcat '[' ']' . map ppDoc . toList

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export covering
ppShowList : (Foldable f, Show a) => f a -> String
ppShowList = show . ppDocList {ann = ()}


||| Pretty print a generic value to stdout.
export covering
pPrint : Show a => a -> IO ()
pPrint = putStrLn . ppShow

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export covering
pPrintList : (Foldable f, Show a) => f a -> IO ()
pPrintList = putStrLn . ppShowList

--------------------------------------------------------------------------------
--          Pretty via PrettyVal
--------------------------------------------------------------------------------

||| Render a value in the `PrettyVal` interface to a `Doc`.
||| The benefit of this function is that `PrettyVal` instances may
||| be derived automatically using generics.
export
dumpDoc : PrettyVal a => a -> Doc ann
dumpDoc = valToDoc . prettyVal

||| Render a value in the `PrettyVal` interface to a `String`.
||| The benefit of this function is that `PrettyVal` instances may
||| be derived automatically using generics.
export
dumpStr : PrettyVal a => a -> String
dumpStr = show . dumpDoc {ann = ()}

||| Render a value using the `PrettyVal` interface
||| and show it to standard out.
export
dumpIO : PrettyVal a => a -> IO ()
dumpIO = putStrLn . dumpStr

--------------------------------------------------------------------------------
--          Pre-processing
--------------------------------------------------------------------------------

||| This type is used to allow pre-processing of values before showing them.
public export
record PreProc a where
  constructor MkPreProc
  preProc : Value -> Value
  val     : a

export
PrettyVal a => PrettyVal (PreProc a) where
  prettyVal (MkPreProc p v) = p (prettyVal v)

||| Hide the given constructors when showing a value.
export
ppHide : (Name -> Bool) -> a -> PreProc a
ppHide p = MkPreProc (hideCon False p)

||| Hide the given constructors when showing a value.
||| In addition, hide values if all of their children were hidden.
export
ppHideNested : (Name -> Bool) -> a -> PreProc a
ppHideNested p = MkPreProc (hideCon True p)
