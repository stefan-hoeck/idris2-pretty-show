module Text.Show.Pretty

import Data.List
import Text.PrettyPrint.Bernardy

import public Text.Show.Value
import public Text.Show.PrettyVal
import public Text.Show.PrettyVal.Derive

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

onLineAfter : {opts : _} -> Doc opts -> Doc opts -> Doc opts
onLineAfter l d = vappend d (indent 2 l)

toDoc : {opts : _} -> Value -> Doc opts
toDoc val =
  case val of
    Con (MkName "") vs => sep $ atoms vs
    Con (MkName c)  [] => line c
    Con (MkName c)  vs => prettyCon Open c (atoms vs)
    InfixCons v1 cvs   => sep (infx v1 cvs)
    Rec (MkName c) fs  => prettyRecord Open c (fields fs)
    Lst vs             => list (docs vs)
    Tuple v1 v2 vs     => tuple (toDoc v1 :: toDoc v2 :: docs vs)
    Neg v              => line "-" <+> atom v
    Natural x          => line x
    Dbl x              => line x
    Chr x              => line x
    Str x              => line x

  where
    atom : Value -> Doc opts
    atom v = if isAtom v then toDoc v else parens (toDoc v)

    -- the explicit list mappings like `atoms`, `docs`, and
    -- `fields` are necessary to convince the totality checker.
    atoms : List Value -> List (Doc opts)
    atoms []        = []
    atoms (x :: xs) = atom x :: atoms xs

    infixAtom : Value -> Doc opts
    infixAtom v = if isInfixAtom v then toDoc v else parens (toDoc v)

    field : (VName,Value) -> Doc opts
    field (MkName s,v) =
      let name := line s <++> equals
          val  := toDoc v
       in ifMultiline (name <++> val) (val `onLineAfter` name)

    fields : List (VName,Value) -> List (Doc opts)
    fields []        = []
    fields (p :: ps) = field p :: fields ps

    docs : List Value -> List (Doc opts)
    docs []        = []
    docs (x :: xs) = toDoc x :: docs xs

    infx : Value -> List (VName,Value) -> List (Doc opts)
    infx v []                  = [infixAtom v]
    infx v ((MkName n,v2)::ps) = (infixAtom v <++> line n) :: infx v2 ps

public export
dfltOpts : LayoutOpts
dfltOpts = Opts 80

||| Pretty print a generic value. Our intention is that the result is
||| equivalent to the 'Show' instance for the original value, except possibly
||| easier to understand by a human.
export %inline
valToDoc : {opts : _} -> Value -> Doc opts
valToDoc = toDoc

||| Pretty print a generic value. Our intention is that the result is
||| equivalent to the 'Show' instance for the original value, except possibly
||| easier to understand by a human.
export %inline
valToStr : Value -> String
valToStr = render dfltOpts . valToDoc

--------------------------------------------------------------------------------
--          Pretty via Show
--------------------------------------------------------------------------------

export %inline
reify : Show a => a -> Maybe Value
reify = parseValue . show

||| Try to show a value, prettily. If we do not understand the value, then we
||| just use its standard 'Show' instance.
export
ppDoc : {opts : _} -> Show a => a -> Doc opts
ppDoc a =
  let txt = show a
   in maybe (fromString txt) valToDoc (parseValue txt)

||| Convert a generic value into a pretty 'String', if possible.
export %inline
ppShow : Show a => a -> String
ppShow = render dfltOpts . ppDoc

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export %inline
ppDocList : {opts : _} -> (Foldable f, Show a) => f a -> Doc opts
ppDocList = list . map ppDoc . toList

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export %inline
ppShowList : (Foldable f, Show a) => f a -> String
ppShowList = render dfltOpts . ppDocList


||| Pretty print a generic value to stdout.
export
pPrint : Show a => a -> IO ()
pPrint = putStrLn . ppShow

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export
pPrintList : (Foldable f, Show a) => f a -> IO ()
pPrintList = putStrLn . ppShowList

--------------------------------------------------------------------------------
--          Pretty via PrettyVal
--------------------------------------------------------------------------------

||| Render a value in the `PrettyVal` interface to a `Doc`.
||| The benefit of this function is that `PrettyVal` instances may
||| be derived automatically using generics.
export
dumpDoc : {opts : _} -> PrettyVal a => a -> Doc opts
dumpDoc = valToDoc . prettyVal

||| Render a value in the `PrettyVal` interface to a `String`.
||| The benefit of this function is that `PrettyVal` instances may
||| be derived automatically using generics.
export
dumpStr : PrettyVal a => a -> String
dumpStr = render dfltOpts . dumpDoc

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
ppHide : (VName -> Bool) -> a -> PreProc a
ppHide p = MkPreProc (hideCon False p)

||| Hide the given constructors when showing a value.
||| In addition, hide values if all of their children were hidden.
export
ppHideNested : (VName -> Bool) -> a -> PreProc a
ppHideNested p = MkPreProc (hideCon True p)
