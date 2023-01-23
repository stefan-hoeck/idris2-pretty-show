module Text.Show.Value

import Data.List1
import Data.Vect
import Derive.Prelude
import Text.Lex
import Text.Parse
import Text.PrettyPrint.Bernardy

%language ElabReflection

%default total

||| A name.
public export
record VName where
  constructor MkName
  unName : String

%runElab derive "VName" [Show,Eq,Ord,FromString,Semigroup,Monoid]

public export
Interpolation VName where interpolate (MkName n) = interpolate n

public export
Pretty VName where
  prettyPrec _ = line . unName

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
data Value = Con VName (List Value)
           | InfixCons Value (List (VName,Value))
           | Rec VName (List (VName,Value))
           | Tuple Value Value (List Value) -- At least two values
           | Lst (List Value)
           | Neg Value
           | Natural String
           | Dbl String
           | Chr String
           | Str String

%runElab derive "Value" [Show, Eq]

export
depth : Value -> Nat
depth v = case v of
               (Con x xs)       => S $ maxDepth xs
               (InfixCons x xs) => S $ maxDepthP xs
               (Rec x xs)       => S $ maxDepthP xs
               (Tuple x y xs)   => S . max (depth x) $ max (depth y) (maxDepth xs)
               (Lst xs)         => S $ maxDepth xs
               (Neg x)          => S $ depth x
               (Natural x)      => 0
               (Dbl x)          => 0
               (Chr x)          => 0
               (Str x)          => 0

  where maxDepth : List Value -> Nat
        maxDepth []       = 0
        maxDepth (h :: t) = max (depth h) (maxDepth t)

        maxDepthP : List (a,Value) -> Nat
        maxDepthP []           = 0
        maxDepthP ((_,h) :: t) = max (depth h) (maxDepthP t)

||| Displays an applied binary operator.
||| If the same operator appears several times in a row,
||| this is treated as a list of infix constructors.
public export
binOp : VName -> Value -> Value -> Value
binOp op pvx pvy =
   case pvy of
        InfixCons pv1 pairs@((op2, pv2) :: xs) =>
          if op2 == op then InfixCons pvx ((op,pvy) :: pairs)
                       else InfixCons pvx [(op,pvy)]
        _ => InfixCons pvx [(op,pvy)]

hidden : (Bool,Value)
hidden = (True, Con "_" [])

toVal : Bool -> Lazy Value -> (Bool,Value)
toVal True  _ = hidden
toVal False v = (False, v)

0 V,VN : Type
V  = Value
VN = VName

parameters (collapse : Bool) (hide : VName -> Bool)

  -- the `Bool` flag is set to `True`, if the wrapped value
  -- was hidden and corresponds to `Con "_" []`.
  val : V -> (Bool,V)

  ops : Bool -> SnocList (VN,V) -> V -> List (VN,V) -> (Bool,V)
  ops h sv v0 []            = toVal h $ InfixCons v0 (sv <>> [])
  ops h sv v0 ((n,v) :: vs) =
    let (h2,w) := val v in ops (h && h2) (sv :< (n,w)) v0 vs

  hrec : Bool -> SnocList (VN,V) -> VN -> List (VN,V) -> (Bool,V)
  hrec h sv nm [] = toVal h $ Rec nm (sv <>> [])
  hrec h sv nm ((n,v) :: vs) = case val v of
    (False, w) => hrec False (sv :< (n,w)) nm vs
    (True,_)   => hrec h sv n vs

  hcon : Bool -> SnocList V -> VN -> List V -> (Bool,V)
  hcon h sv n [] = toVal h $ Con n (sv <>> [])
  hcon h sv n (v :: vs) = let (h2,w) := val v in hcon (h && h2) (sv :< w) n vs

  lst : Bool -> SnocList V -> List V -> (Bool,V)
  lst h sv [] = toVal h $ Lst (sv <>> [])
  lst h sv (v :: vs) = let (h2,w) := val v in lst (h && h2) (sv :< w) vs

  val (Con x xs) =
    if hide x then hidden else hcon (isCons xs && collapse) [<] x xs

  val (InfixCons v ps) =
    if any (hide . fst) ps then hidden
    else let (b,w) := val v in ops (b && collapse) [<] w ps

  val (Rec x xs) =
    if hide x then hidden else hrec (isCons xs && collapse) [<] x xs

  val (Lst xs) = lst (isCons xs && collapse) [<] xs

  val (Neg v) = let (b,w) := val v in (b,w)

  val (Tuple v1 v2 vs) =
    let (b1,w1)     := val v1
        (b2,w2)     := val v2
        (b3,Lst ws) := lst (b1 && b2 && collapse) [<] vs | _ => hidden
     in toVal b3 $ Tuple w1 w2 ws

  val (Natural x) = (False,Natural x)
  val (Dbl x)     = (False,Dbl x)
  val (Chr x)     = (False,Chr x)
  val (Str x)     = (False,Str x)

  ||| Hide constructors matching the given predicate.
  ||| If the hidden value is in a record, we also hide
  ||| the corresponding record field.
  |||
  ||| If the boolean flag is true, then we also hide
  ||| constructors all of whose fields were hidden.
  export
  hideCon : Value -> Value
  hideCon = snd . val

--------------------------------------------------------------------------------
--          Tokenizer
--------------------------------------------------------------------------------

isIdentStart : Char -> Bool
isIdentStart '_' = True
isIdentStart  x  = isAlpha x

isIdentTrailing : Char -> Bool
isIdentTrailing '\'' = True
isIdentTrailing '_'  = True
isIdentTrailing x    = isAlphaNum x || x > chr 160

lexident : Lexer
lexident = pred isIdentStart <+> preds0 isIdentTrailing

namespacedIdent : Lexer
namespacedIdent = lexident <+> many (is '.' <+> lexident)

public export
data Token : Type where
  Lit      : Value -> Token
  Ident    : String -> Token
  Op       : String -> Token
  Equals   : Token
  Comma    : Token
  BracketO : Token
  BracketC : Token
  BraceO   : Token
  BraceC   : Token
  ParenO   : Token
  ParenC   : Token
  Space    : Token

%runElab derive "Token" [Show,Eq]

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

op : Lexer
op = preds isOpChar

isSymbol : Char -> Bool
isSymbol c = c `elem` (unpack "()[]{},")

parseOp : SnocList Char -> Token
parseOp [<'='] = Equals
parseOp s      = Op (pack s)

natLit : AutoShift True Char
natLit ('0' :: 'x' :: t) = takeWhile1 {b} isHexDigit t
natLit ('0' :: 'X' :: t) = takeWhile1 {b} isHexDigit t
natLit ('0' :: 'o' :: t) = takeWhile1 {b} isOctDigit t
natLit ('0' :: 'b' :: t) = takeWhile1 {b} isBinDigit t
natLit t                 = takeWhile1 {b} isDigit t

tokParens : Tok True Char Token
tokParens ('(' :: t) = Succ ParenO t
tokParens (')' :: t) = Succ ParenC t
tokParens ('{' :: t) = Succ BraceO t
tokParens ('}' :: t) = Succ BraceC t
tokParens ('[' :: t) = Succ BracketO t
tokParens (']' :: t) = Succ BracketC t
tokParens (',' :: t) = Succ Comma t
tokParens _          = Fail

dbl : SnocList Char -> Token
dbl sc =
  if all isDigit sc then Lit (Natural $ pack sc) else Lit (Dbl $ pack sc)

natural : Lexer
natural = autoLift {b = True} natLit <+> reject (oneOf ['.', 'e', 'E'])

unesc : SnocList Char -> List Char -> SnocList Char

unescDec, unescHex, unescOct : Nat -> SnocList Char -> List Char -> SnocList Char

unescOct k sc (x :: xs) =
  if isOctDigit x
     then unescOct (k * 8 + octDigit x) sc xs
     else unesc (sc :< cast k) xs
unescOct k sc [] = sc :< cast k

unescDec k sc (x :: xs) =
  if isDigit x
     then unescDec (k * 10 + digit x) sc xs
     else unesc (sc :< cast k) xs
unescDec k sc [] = sc :< cast k

unescHex k sc (x :: xs) =
  if isHexDigit x
     then unescHex (k * 16 + hexDigit x) sc xs
     else unesc (sc :< cast k) xs
unescHex k sc [] = sc :< cast k

unesc sc ['"']                = sc
unesc sc ('\\' :: '"' :: xs)  = unesc (sc :< '"') xs
unesc sc ('\\' :: 'n' :: xs)  = unesc (sc :< '\n') xs
unesc sc ('\\' :: 't' :: xs)  = unesc (sc :< '\t') xs
unesc sc ('\\' :: 'r' :: xs)  = unesc (sc :< '\r') xs
unesc sc ('\\' :: 'f' :: xs)  = unesc (sc :< '\f') xs
unesc sc ('\\' :: 'b' :: xs)  = unesc (sc :< '\b') xs
unesc sc ('\\' :: '\\' :: xs) = unesc (sc :< '\\') xs
unesc sc ('\\' :: c :: xs@(x :: t)) =
  if (toLower c == 'x' && isHexDigit x) then unescHex (hexDigit x) sc t
  else if (c == 'o' && isOctDigit x) then unescOct (octDigit x) sc t
  else if isDigit c then unescDec (digit c) sc xs
  else unesc (sc :< c) xs
unesc sc (x :: xs)            = unesc (sc :< x) xs
unesc sc []                   = sc

export
tokens : Tokenizer Token
tokens =
  Match [
     (natural, Lit . Natural . pack)
   , (reject (is '-') <+> autoLift number, dbl)
   , (stringLit, Lit . Str . pack)
   , (charLit, Lit . Chr . pack)
   , (namespacedIdent, Ident . pack)
   , (op, parseOp)
   , (spaces, const Space)
   ] <|> Direct tokParens

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

AnyRule : Bool -> Type -> Type
AnyRule b = Grammar b () Token Void

Rule : Type -> Type
Rule = AnyRule True

EmptyRule : Type -> Type
EmptyRule = AnyRule False

lit : Rule Value
lit = terminal $ \case Lit v => Just v; _ => Nothing

ident : Rule VName
ident = terminal $ \case Ident v => Just (MkName v); _ => Nothing

operator : Rule VName
operator = terminal $ \case Op v => Just (MkName v); _ => Nothing

minus : Rule ()
minus = is (Op "-")

comma : Rule ()
comma = is Comma

equals : Rule ()
equals = is Equals

parens : AnyRule b a -> Rule a
parens = between (is ParenO) (is ParenC)

brackets : AnyRule b a -> Rule a
brackets = between (is BracketO) (is BracketC)

braces : AnyRule b a -> Rule a
braces = between (is BraceO) (is BraceC)

identOrOp : Rule VName
identOrOp = Try $ ident <|> map (\n => MkName "(\{n})") (parens operator)

value,applied,negApplied,negated,list,tuple,con,rec,infx : Rule Value

values : EmptyRule (List Value)
values = sepBy comma value

value =
      lit
  <|> negated
  <|> list
  <|> Try tuple
  <|> Try rec
  <|> con
  <|> infx

applied =
      lit
  <|> map (`Con` []) identOrOp
  <|> tuple
  <|> list

negApplied = map Neg applied

negated = minus >>= \_ => negApplied

tuple = do
  _ <- is ParenO
  vs <- values
  _ <- is ParenC
  pure $ case vs of
    []        => Con "()" []
    [x]       => x
    x1::x2::t => Tuple x1 x2 t

list = do
  _ <- is BracketO
  vs <- values
  _ <- is BracketC
  pure $ Lst vs

pair : Rule (VName,Value)
pair = [| (,) identOrOp (equals *> value) |]

rec = [| Rec identOrOp (braces $ sepBy comma pair) |]

con = [| Con identOrOp (many applied) |]

infxOps : Rule (Value, List (VName, Value))

moreOps : Value -> VName -> Rule (Value, List (VName,Value))

infx = uncurry InfixCons <$> infxOps

infxOps = do
  v  <- applied
  op <- operator
  moreOps v op

moreOps v op =
  map (\(v2,ps) => (v,(op,v2) :: ps)) infxOps <|>
  map (\v2 => (v, [(op,v2)])) applied

export
parseValueE : String -> Either (ReadError Token Void) Value
parseValueE s = snd <$> lexAndParse Virtual tokens (/= Space) value () s

export
parseValue : String -> Maybe Value
parseValue = either (const Nothing) Just . parseValueE
