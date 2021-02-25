module Text.Show.Value

import Data.Vect
import Data.List1
import Generics.Derive
import Text.Lexer
import Text.Parser
import Text.PrettyPrint.Prettyprinter

%hide Language.Reflection.TT.Name

%language ElabReflection

%default total

||| A name.
public export
record Name where
  constructor MkName
  unName : String

%runElab derive "Text.Show.Value.Name" [Generic,Meta,Show,Eq,Ord,Semigroup]

public export
FromString Name where fromString = MkName

public export
Pretty Name where
  pretty = pretty . unName

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
           | Rec Name (List (Name,Value))
           | Tuple Value Value (List Value) -- At least two values
           | Lst (List Value)
           | Neg Value
           | Natural String
           | Dbl String
           | Chr String
           | Str String

%runElab derive "Value" [Generic,Meta]

export covering
Eq Value where (==) = genEq

export covering
Show Value where showPrec = genShowPrec

||| Displays an applied binary operator.
||| If the same operator appears several times in a row,
||| this is treated as a list of infix constructors.
public export
binOp : Name -> Value -> Value -> Value
binOp op pvx pvy =
   case pvy of
        InfixCons pv1 pairs@((op2, pv2) :: xs) =>
          if op2 == op then InfixCons pvx ((op,pvy) :: pairs)
                       else InfixCons pvx [(op,pvy)]
        _ => InfixCons pvx [(op,pvy)]

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

           Tuple v1 v2 vs  => let vs2 = delMany (v1 :: v2 :: Vect.fromList vs)
                               in map (\(a::b::xs) => Tuple a b (toList xs)) vs2

           Lst []          => Just val
           Lst vs          => Lst <$> delMany vs
           Neg v           => Neg <$> delMaybe v
           Natural _       => Just val
           Dbl _           => Just val
           Chr _           => Just val
           Str _           => Just val

--------------------------------------------------------------------------------
--          Tokenizer
--------------------------------------------------------------------------------

-- taken from the actual Idris2 tokenizer
data Flavour = Capitalised | Normal

isIdentStart : Flavour -> Char -> Bool
isIdentStart _           '_' = True
isIdentStart Capitalised  x  = isUpper x || x > chr 160
isIdentStart _            x  = isAlpha x || x > chr 160

isIdentTrailing : Char -> Bool
isIdentTrailing '\'' = True
isIdentTrailing '_'  = True
isIdentTrailing x    = isAlphaNum x || x > chr 160

ident : Flavour -> Lexer
ident flavour =   (pred $ isIdentStart flavour)
              <+> (many $ pred isIdentTrailing )

identNormal : Lexer
identNormal = ident Normal

namespaceIdent : Lexer
namespaceIdent = ident Capitalised <+> many (is '.' <+> ident Capitalised <+> expect (is '.'))

namespacedIdent : Lexer
namespacedIdent = namespaceIdent <+> opt (is '.' <+> identNormal)

public export
data ShowToken = StringLit String
               | NatLit    String
               | DblLit    String
               | CharLit   String
               | Ident     String
               | Symbol    String
               | Op        String
               | Space     String

%runElab derive "ShowToken" [Generic,Meta,Show,Eq]

binDigit : Lexer
binDigit = pred (\c => c == '0' || c == '1')

binDigits : Lexer
binDigits = some binDigit

binLit : Lexer
binLit = exact "0b" <+> binDigits

octLit : Lexer
octLit = exact "0o" <+> octDigits

holeIdent : Lexer
holeIdent = is '?' <+> identNormal

dotIdent : Lexer
dotIdent = is '.' <+> identNormal

pragma : Lexer
pragma = is '%' <+> identNormal

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

op : Lexer
op = some (pred isOpChar)

isSymbol : Char -> Bool
isSymbol c = c `elem` (unpack "()[]{},")

parseOp : String -> ShowToken
parseOp "=" = Symbol "="
parseOp s   = Op s

anyIdent : Lexer
anyIdent =  choice {t = List} [ namespacedIdent
                              , identNormal
                              , dotIdent
                              , holeIdent
                              , pragma
                              ]

doubleLit : Lexer
doubleLit = digits <+> is '.' <+> digits <+> opt
             ((is 'e' <|> is 'E') <+> opt (is '-' <|> is '+') <+> digits)

tokens : TokenMap ShowToken
tokens = [ (doubleLit, DblLit)
         , (binLit <|> octLit <|> hexLit <|> digits, NatLit)
         , (stringLit, StringLit)
         , (charLit, CharLit)
         , (anyIdent, Ident)
         , (op, parseOp)
         , (pred isSymbol, Symbol)
         , (spaces, Space)
         ]

public export
data Err = LexErr Int Int String
         | ParseErr String (List ShowToken)

%runElab derive "Err" [Generic,Meta,Show,Eq]

export
lex : String -> Either Err (List ShowToken)
lex str = case lex tokens str of
               (ts, (_, _, "")) => Right . filter notSpace $ map tok ts
               (_, (a,b,c))     => Left $ LexErr a b c
  where notSpace : ShowToken -> Bool
        notSpace (Space _) = False
        notSpace _         = True

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

Rule : Type -> Type
Rule = Grammar ShowToken True

EmptyRule : Type -> Type
EmptyRule = Grammar ShowToken False

constant : Rule Value
constant = terminal "Expected constant"
                     \case CharLit c    => Just $ Chr c
                           DblLit d     => Just $ Dbl d
                           StringLit s  => Just $ Str s
                           NatLit s     => Just $ Natural s
                           _            => Nothing

identRule : Rule Name
identRule = terminal "Expected identifier"
                     \case Ident s => Just $ MkName s
                           _       => Nothing

operator : Rule Name
operator = terminal "Expected operator"
                    \case Op s => Just $ MkName s
                          _    => Nothing

symbol : String -> Rule ()
symbol s = terminal ("Expected " ++ s)
                    \case Symbol s2 => if s == s2 then Just ()
                                                  else Nothing
                          _         => Nothing

comma : Rule ()
comma = symbol ","

equals : Rule ()
equals = symbol "="

parens : {c : _} -> Inf (Grammar ShowToken c a) -> Rule a
parens = between (symbol "(") (symbol ")")

brackets : {c : _} -> Inf (Grammar ShowToken c a) -> Rule a
brackets = between (symbol "[") (symbol "]")

braces : {c : _} -> Inf (Grammar ShowToken c a) -> Rule a
braces = between (symbol "{") (symbol "}")

identOrOp : Rule Name
identOrOp = identRule <|> 
            map (\(MkName n) => MkName ("(" ++ n ++ ")")) (parens operator)

unit : Rule Value
unit =  symbol "(" *> symbol ")" $> Con "()" []

mutual
  covering
  value : Rule Value
  value = choice {t = List} [ constant 
                            , unit
                            , negated
                            , list
                            , tuple
                            , rec
                            , con
                            , infx
                            ]

  covering
  applied : Rule Value
  applied =   constant 
          <|> map (\n => Con n []) identOrOp
          <|> negated
          <|> list
          <|> tuple
          <|> parens value

  covering
  negated : Rule Value
  negated = symbol "-" *> map Neg applied

  covering
  tuple : Rule Value
  tuple = parens $ do (v1::v2::vs) <- sepBy comma value
                        | vs => fail "Tuple needs at least two values"
                      pure (Tuple v1 v2 vs)

  covering
  list : Rule Value
  list = Lst <$> brackets (sepBy comma value)

  covering
  pair : Rule (Name,Value)
  pair = [| (,) identOrOp (equals *> value) |]

  covering
  rec : Rule Value
  rec = [| Rec identOrOp (braces $ sepBy comma pair) |]
  
  covering
  con : Rule Value
  con = [| Con identOrOp (many applied) |]

  covering
  infx : Rule Value
  infx = uncurry InfixCons <$> go
    where go : Rule (Value,List (Name,Value))
          go = do v    <- applied
                  op   <- operator
                  map (\(v2,ps) => (v,(op,v2) :: ps)) go <|>
                  map (\v2 => (v, [(op,v2)])) applied

export
parseValueE : String -> Either Err Value
parseValueE str = lex str >>= doParse
  where doParse : List ShowToken -> Either Err Value
        doParse ts =
          case parse value ts of
               Left (Error str ts) => Left $ ParseErr str ts
               Right (v,[])        => Right v
               Right (_,ts)        => Left $ ParseErr "Expected end of input" ts

export
parseValue : String -> Maybe Value
parseValue = either (const Nothing) Just . parseValueE
