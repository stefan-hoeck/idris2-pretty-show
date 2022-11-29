module Text.Show.PrettyVal.Derive

import System.Clock
import System.File
import Text.Lexer
import Text.Show.PrettyVal
import Text.Show.Value
import public Derive.Show

%language ElabReflection

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- Displays an applied constructer in record syntax.
-- This is called, if all arguments have user-defined names.
public export
rec : String -> List (Value,String) -> Value
rec con ps = Rec (MkName con) $ map (\(v,n) => (MkName n, v)) ps
  where named : Value -> String -> (VName,Value)
        named v name = (MkName name, v)

-- Displays an applied constructer with unnamed arguments.
public export
other : String -> List Value -> Value
other con = Con (MkName con)

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Name of the top-level function implementing the derived prettyVal function.
public export
(.prettyValName) : Named a => a -> Name
v.prettyValName = UN $ Basic "prettyVal\{v.nameStr}"

||| General type of a `prettyVal` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalPrettyValType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalPrettyValType is arg = piAll `(~(arg) -> Value) is

||| Top-level function declaration implementing the `prettyVal` function for
||| the given data type.
export
prettyValClaim : (p : ParamTypeInfo) -> Decl
prettyValClaim p =
  let tpe := generalPrettyValType (allImplicits p "PrettyVal") p.applied
   in public' p.prettyValName tpe

||| Name of the derived interface implementation.
public export
(.prettyValImplName) : Named a => a -> Name
v.prettyValImplName = UN $ Basic "prettyValImpl\{v.nameStr}"

||| Top-level declaration of the `PrettyVal` implementation for the given data type.
export
prettyValImplClaim : (p : ParamTypeInfo) -> Decl
prettyValImplClaim p = implClaim p.prettyValImplName (implType "PrettyVal" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `PrettyVal` implementation for the given data type.
export
prettyValImplDef : Named a => a -> Decl
prettyValImplDef p =
  def p.prettyValImplName
    [var p.prettyValImplName .= var "MkPrettyVal" .$ var p.prettyValName]

parameters (nms : List Name)

  namedRHS :
       Name
    -> SnocList TTImp
    -> (as : Vect n Arg)
    -> (ns : Vect n Name)
    -> TTImp
  namedRHS n st (MkArg M0 ExplicitArg (Just nm) _ :: xs) (y :: ys) =
    let str := primVal (Str "\{nameStr nm}")
        t   := `(MkPair (Chr "_") ~(str))
     in namedRHS n (st :< t) xs ys
  namedRHS n st (MkArg _  ExplicitArg (Just nm) t :: xs) (y :: ys) =
    let prettyValn := assertIfRec nms t `(prettyVal ~(var y))
        str   := primVal (Str "\{nameStr nm}")
        t     := `(MkPair ~(prettyValn) ~(str))
     in namedRHS n (st :< t) xs ys
  namedRHS n st (_ :: xs) (_ :: ys) = namedRHS n st xs ys
  namedRHS n Lin      [] [] = `(Con (MkName ~(n.namePrim)) [])
  namedRHS n sx       [] [] =
    let args := foldr (\e,acc => `(~(e) :: ~(acc))) `(Prelude.Nil) sx
     in `(rec ~(n.namePrim) ~(args))

  -- Right-hand side of a single prettyVal clause.
  -- String conversion for a set of constructor arguments.
  -- Checks if the argument types are safely recursive, that is, contains
  -- one of the data type names listed in `nms`. If so, prefixes
  -- the generated function call with `assert_total`.
  rhs : Name -> SnocList TTImp -> Vect n Arg -> Vect n Name -> TTImp
  rhs n st (x :: xs) (y :: ys) = case isExplicit x of
    True  => case x.count of
      M0 => primVal (Str " _")
      _  => let t := assertIfRec nms x.type `(prettyVal ~(var y))
             in rhs n (st :< t) xs ys
    False => rhs n st xs ys
  rhs n Lin []        [] = `(Con (MkName ~(n.namePrim)) [])
  rhs n sx  []        [] =
    let args := foldr (\e,acc => `(~(e) :: ~(acc))) `(Prelude.Nil) sx
     in `(other ~(n.namePrim) ~(args))

  export
  prettyValClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  prettyValClauses fun ti =
    let b := namedType ti
     in map (clause b) ti.cons
    where clause : Bool -> Con ti.arty ti.args -> Clause
          clause b c =
            let ns  := freshNames "x" c.arty
                bc  := bindCon c ns
                lhs := maybe bc ((.$ bc) . var) fun
             in lhs .=
                  if b then namedRHS c.name Lin c.args ns
                       else rhs c.name Lin c.args ns

  export
  prettyValDef : Name -> TypeInfo -> Decl
  prettyValDef fun ti = def fun (prettyValClauses (Just fun) ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Derive an implementation of `PrettyVal a` for a custom data type `a`.
|||
||| Note: This is mainly to be used for indexed data types. Consider using
|||       `derive` together with `Derive.PrettyVal.PrettyVal` for parameterized data types.
export %macro
derivePrettyVal : Elab (PrettyVal f)
derivePrettyVal = do
  Just tpe <- goal
    | Nothing => fail "Can't infer goal"
  let Just (resTpe, nm) := extractResult tpe
    | Nothing => fail "Invalid goal type: \{show tpe}"
  ti <- getInfo' nm

  let impl :=  lambdaArg {a = Name} "x"
           .=> iCase `(x) implicitFalse (prettyValClauses [ti.name] Nothing ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkPrettyVal" .$ impl

||| Generate declarations and implementations for `PrettyVal` for a given data type.
export
PrettyVal : List Name -> ParamTypeInfo -> List TopLevel
PrettyVal nms p =
  [ TL (prettyValClaim p) (prettyValDef nms p.prettyValName p.info)
  , TL (prettyValImplClaim p) (prettyValImplDef p)
  ]

%runElab derive "Bool" [PrettyVal]

%runElab derive "Ordering" [PrettyVal]

%runElab derive "Maybe" [PrettyVal]

%runElab derive "Either" [PrettyVal]

%runElab derive "List1" [PrettyVal]

%runElab derive "Prec" [PrettyVal]

-- Pretty

%runElab derive "VName" [PrettyVal]

%runElab derive "Value" [PrettyVal]

%runElab derive "ShowToken" [PrettyVal]

%runElab derive "Bounds" [PrettyVal]

%runElab derive "WithBounds" [PrettyVal]

%runElab derive "Err" [PrettyVal]

-- System

%runElab derive "System.File.Mode.Mode" [PrettyVal]

%runElab derive "FileError" [PrettyVal]

%runElab derive "FileMode" [PrettyVal]

%runElab derive "Permissions" [PrettyVal]

%runElab derive "ClockType" [PrettyVal]

-- Reflection

%runElab derive "ModuleIdent" [PrettyVal]

%runElab derive "VirtualIdent" [PrettyVal]

%runElab derive "OriginDesc" [PrettyVal]

%runElab derive "FC" [PrettyVal]

%runElab derive "NameType" [PrettyVal]

%runElab derive "PrimType" [PrettyVal]

%runElab derive "Constant" [PrettyVal]

%runElab derive "Namespace" [PrettyVal]

%runElab derive "UserName" [PrettyVal]

%runElab derive "Language.Reflection.TT.Name" [PrettyVal]

%runElab derive "Count" [PrettyVal]

%runElab derive "PiInfo" [PrettyVal]

%runElab derive "LazyReason" [PrettyVal]

%runElab derive "TotalReq" [PrettyVal]

%runElab derive "Visibility" [PrettyVal]

%runElab derive "BindMode" [PrettyVal]

%runElab derive "UseSide" [PrettyVal]

%runElab derive "DotReason" [PrettyVal]

%runElab derive "DataOpt" [PrettyVal]

%runElab derive "WithFlag" [PrettyVal]

%runElab derive "BuiltinType" [PrettyVal]

%runElab deriveMutual
  [ "TTImp"
  , "IField"
  , "IFieldUpdate"
  , "AltType"
  , "FnOpt"
  , "ITy"
  , "Data"
  , "Record"
  , "Clause"
  , "Decl"
  ] [PrettyVal]
