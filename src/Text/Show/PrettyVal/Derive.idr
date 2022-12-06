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

||| General type of a `prettyVal` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalPrettyValType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalPrettyValType is arg = piAll `(~(arg) -> Value) is

||| Top-level function declaration implementing the `prettyVal` function for
||| the given data type.
export
prettyValClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
prettyValClaim fun p =
  let tpe := generalPrettyValType (allImplicits p "PrettyVal") p.applied
   in public' fun tpe

||| Top-level declaration of the `PrettyVal` implementation for the given data type.
export
prettyValImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
prettyValImplClaim impl p = implClaim impl (implType "PrettyVal" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `PrettyVal` implementation for the given data type.
export
prettyValImplDef : (fun, impl : Name) -> Decl
prettyValImplDef f i = def i [var i .= var "MkPrettyVal" .$ var f]

parameters (nms : List Name)
  arg : BoundArg 1 Explicit -> TTImp
  arg (BA (MkArg M0 _ _ _) _   _) = `(Chr "_")
  arg (BA (MkArg _  _ _ t) [x] _) = assertIfRec nms t `(prettyVal ~(x))

  rhs : Name -> SnocList TTImp -> TTImp
  rhs n st = `(other ~(n.namePrim) ~(listOf st))

  narg : BoundArg 1 NamedExplicit -> TTImp
  narg (BA a [x]   _) =
    let nm := (argName a).namePrim
     in case a.count of
       M0 => `(MkPair ~(nm) (Chr "_"))
       _  =>
         let pv := assertIfRec nms a.type `(prettyVal ~(x))
          in `(MkPair ~(pv) ~(nm))

  nrhs : Name -> SnocList TTImp -> TTImp
  nrhs n st  = `(rec ~(n.namePrim) ~(listOf st))

  export
  pvClauses : (fun : Maybe Name) -> TypeInfo -> List Clause
  pvClauses fun ti = map clause ti.cons
    where
      lhs : TTImp -> TTImp
      lhs bc = maybe bc ((.$ bc) . var) fun

      clause : Con ti.arty ti.args -> Clause
      clause c = case all namedArg c.args of
        True  => accumArgs namedExplicit lhs (nrhs c.name) narg c
        False => accumArgs explicit lhs (rhs c.name) arg c

  export
  prettyValDef : Name -> TypeInfo -> Decl
  prettyValDef fun ti = def fun (pvClauses (Just fun) ti)

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
           .=> iCase `(x) implicitFalse (pvClauses [ti.name] Nothing ti)

  logMsg "derive.definitions" 1 $ show impl
  check $ var "MkPrettyVal" .$ impl

||| Generate declarations and implementations for `PrettyVal` for a given data type.
export
PrettyVal : List Name -> ParamTypeInfo -> Res (List TopLevel)
PrettyVal nms p =
  let fun  := funName p "prettyVal"
      impl := implName p "PrettyVal"
   in Right [ TL (prettyValClaim fun p) (prettyValDef nms fun p.info)
            , TL (prettyValImplClaim impl p) (prettyValImplDef fun impl)
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
