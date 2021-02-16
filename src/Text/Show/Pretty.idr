module Text.Show.Pretty

import Data.List
import Text.PrettyPrint.Prettyprinter

import public Text.Show.Value
import public Text.Show.PrettyVal

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

mutual
  toDoc : Value -> Doc ann
  toDoc (Con c vs) = ppCon c vs

  toDoc (InfixCons v1 cvs) = hang_sep (go v1 cvs)
    where
    go : Value -> List (Name,Value) -> List (Doc ann)
    go v []             = [ppInfixAtom v]
    go v ((n,v2)::cvs') = (ppInfixAtom v <++> pretty n) :: go v2 cvs'
    
    hang_sep : List (Doc ann) -> Doc ann
    hang_sep []      = neutral
    hang_sep (x::xs) = hangAfter x 2 (sep xs)

  toDoc (Rec c fs) = hangAfter (pretty c) 2 $ block '{' '}' (map ppField fs)
    where ppField : (Name,Value) -> Doc ann
          ppField (x,v) = hangAfter (pretty x <++> pretty '=')
                                    2
                                    (toDoc v)
  toDoc (Lst vs)    = block '[' ']' (map toDoc vs)
  toDoc (Tuple vs)  = block '(' ')' (map toDoc vs)
  toDoc (Neg v)     = pretty '-' <++> ppAtom v
  toDoc (Natural x) = pretty x
  toDoc (Dbl x)     = pretty x
  toDoc (Chr x)     = pretty x
  toDoc (Str x)     = pretty x

  ppCon : Name -> List Value -> Doc ann
  ppCon (MkName "") vs = sep (map ppAtom vs)
  ppCon (MkName c)  vs = hangAfter (pretty c) 2 (sep $ map ppAtom vs)

  ppAtom : Value -> Doc ann
  ppAtom v = if isAtom v then toDoc v else parens (toDoc v)

  ppInfixAtom : Value -> Doc ann
  ppInfixAtom v = if isInfixAtom v then toDoc v else parens (toDoc v)

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

export
reify : Show a => a -> Maybe Value
reify = parseValue . show

||| Try to show a value, prettily. If we do not understand the value, then we
||| just use its standard 'Show' instance.
export
ppDoc : Show a => a -> Doc ann
ppDoc a = let txt = show a
           in maybe (fromString txt) valToDoc (parseValue txt)

||| Convert a generic value into a pretty 'String', if possible.
export
ppShow : Show a => a -> String
ppShow = show . ppDoc {ann = ()}

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export
ppDocList : (Foldable f, Show a) => f a -> Doc ann
ppDocList = blockWith vcat '[' ']' . map ppDoc . toList

||| Pretty print something that may be converted to a list as a list.
||| Each entry is on a separate line, which means that we don't do clever
||| pretty printing, and so this works well for large strucutures.
export
ppShowList : (Foldable f, Show a) => f a -> String
ppShowList = show . ppDocList {ann = ()}


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

-- instance Show a => Show (PreProc a) where
--   showsPrec p (PreProc f a) cs =
--     case parseValue txt of
--       Nothing -> txt ++ cs
--       Just v  -> wrap (valToStr (f v))
--     where
--     txt    = showsPrec p a ""
--     wrap t = case (t,txt) of
--               (h:_,'(':_) | h /= '(' -> '(' : (t ++ ')' : cs)
--               _ -> t ++ cs
-- 

||| Hide the given constructors when showing a value.
export
ppHide : (Name -> Bool) -> a -> PreProc a
ppHide p = MkPreProc (hideCon False p)

||| Hide the given constructors when showing a value.
||| In addition, hide values if all of their children were hidden.
export
ppHideNested : (Name -> Bool) -> a -> PreProc a
ppHideNested p = MkPreProc (hideCon True p)

-- module Text.Show.Pretty
--   ( -- * Generic representation of values
--   , valToHtmlPage
-- 
-- 
--     -- * Rendering values to Html
--   , valToHtml, HtmlOpts(..), defaultHtmlOpts, htmlPage, Html(..)
-- 
