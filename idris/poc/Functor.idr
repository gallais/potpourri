module Functor

import Data.Maybe
import Data.Nat
import Data.String
import Decidable.Equality
import Language.Reflection

%language ElabReflection
%default total

data FunIs : Name -> TTImp -> Type where
  FVar : FunIs t (IVar fc t)
  FApp : FunIs t f -> FunIs t (IApp fc f a)
  FNamedApp : FunIs t f -> FunIs t (INamedApp fc f n a)
  FAutoApp : FunIs t f -> FunIs t (IAutoApp fc f a)

getFn : (t : TTImp) -> Maybe (f : Name ** FunIs f t)
getFn (IVar _ f) = Just (f ** FVar)
getFn (IApp _ f t) = do
  (v ** prf) <- getFn f
  pure (v ** FApp prf)
getFn (INamedApp _ f _ t) = do
  (v ** prf) <- getFn f
  pure (v ** FNamedApp prf)
getFn (IAutoApp _ f t) = do
  (v ** prf) <- getFn f
  pure (v ** FAutoApp prf)
getFn _ = Nothing

data SPosIn : (t, x : Name) -> TTImp -> Type
data FreeOf : Name -> TTImp -> Type

data SPosIn : (t, x : Name) -> TTImp -> Type where
  SPVar : SPosIn t x (IVar fc x)
  SPTyp : FunIs t f -> SPosIn t x (IApp fc f (IVar fc' x))
  SPPi  : FreeOf x a -> SPosIn t x b -> SPosIn t x (IPi fc rig pinfo nm a b)
  SFree : FreeOf x a -> SPosIn t x a

data FreeOf : Name -> TTImp -> Type where
  TrustMe : FreeOf a x

check : (t, x : Name) -> (ty : TTImp) -> Maybe (Either (SPosIn t x ty) (FreeOf x ty))
check t x (IVar fc y) = pure $ case decEq x y of
  Yes Refl => Left SPVar
  No _ => Right TrustMe
check t x (IPi fc rig pinfo nm a b) = do
  Right p <- check t x a
    | _ => Nothing
  Left q <- check t x b
    | _ => Just (Right TrustMe)
  Just (Left (SPPi p q))
check t x (IApp fc f (IVar _ y)) = do
  let Yes Refl = decEq x y
       | _ => Nothing
  (hd ** prf) <- getFn f
  case decEq t hd of
    Yes Refl => Just (Left (SPTyp prf))
    No diff => Nothing
check _ _ _ = Nothing

exampleType : (a : Name) -> SPosIn `{List} a ?
exampleType a = case check `{List} a `(Nat -> List a) of
  Just (Left prf) => prf
  _ => ?h

{-
test : (a : Type) -> exampleType `{a} === ?a
test = ?prf
-}

target : FC -> {f : TTImp} -> SPosIn t x f -> (y : Name) -> TTImp
target fc SPVar y = IVar fc y
target fc (SPTyp {f} _) y = IApp fc f (IVar fc y)
target fc (SPPi {rig, pinfo, nm, a} _ prf) y = IPi fc rig pinfo nm a (target fc prf y)
target fc (SFree _) _ = f

exampleTarget : (a, b : Name) -> TTImp
exampleTarget a b = target emptyFC (exampleType a) b

test2 : (a, b : Type) -> exampleTarget `{a} `{b} === ?zg
test2 a b = ?prf2

infixr 5 ~>

functorType : FC -> (a, b : Name) -> TTImp
functorType fc a b = (IVar fc a ~> IVar fc b) ~> (exampleTarget a a ~> exampleTarget a b) where

  (~>) : TTImp -> TTImp -> TTImp
  s ~> t = IPi fc MW ExplicitArg Nothing s t

functorFun : FC -> {f : TTImp} -> SPosIn t x f -> (rec, f : Name) -> TTImp -> TTImp
functorFun fc SPVar rec f t = IApp fc (IVar fc f) t
functorFun fc (SPTyp y) rec f t = IApp fc (IApp fc (IVar fc rec) (IVar fc f)) t
functorFun fc (SPPi {rig, pinfo, nm, a} _ z) rec f t
  = let nm = fromMaybe (UN $ Basic "x") nm in
    ILam fc rig pinfo (Just nm) a (functorFun fc z rec f (IApp fc t (IVar fc nm)))
functorFun fc (SFree y) rec f t = t

exampleFun : (a -> b) -> (Nat -> List a) -> (Nat -> List b)
exampleFun f t = %runElab (check $ functorFun emptyFC (exampleType `{a}) `{map} `{f} `(t))

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

isType : Name -> Elab (List (Name, TTImp))
isType ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [] => fail "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => fail "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => fail "\{show ty} is ambiguous"
    cs <- getCons ty
    for cs $ \ n => do
      [(_, ty)] <- getType n
         | _ => fail "\{show n} is ambiguous"
      pure (n, ty)

explicits : TTImp -> List TTImp
explicits (IPi fc rig ExplicitArg x a b) = a :: explicits b
explicits (IPi fc rig pinfo x a b) = explicits b
explicits _ = []

apply : FC -> TTImp -> List TTImp -> TTImp
apply fc = foldl (IApp fc)

namespace Functor

  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           Elab (Functor f)
  derive = do
    Just (IApp _ (IVar _ functor) (IVar _ f)) <- goal
      | _ => fail "Invalid goal: cannot derive functor"
    when (`{Prelude.Interfaces.Functor} /= functor) $
      logMsg "derive.functor" 1 (show functor)
    logMsg "derive.functor" 1 (show f)
    cs <- isType f
    logMsg "derive.functor.constructors" 1 $
      unlines $ "" :: map (\ (n, ty) => "  \{show n} : \{show ty}") cs
    let fc = emptyFC
    let mapName = UN (Basic $ "map" ++ show (dropNS f))
    cls <- for cs $ \ (cName, ty) => do
             let args = explicits ty
             logMsg "derive.functor.clauses" 10 $ "\{show cName} (\{joinBy ", " (map show args)})"
             let funName = UN $ Basic "f"
             let fun  = IVar fc funName
             let vars = map (IVar fc . UN . Basic . ("x" ++) . show . pred)
                      $ zipWith const [1..length args] args -- fix because [1..0] is [1,0]
             recs <- for (zip vars args) $ \ (v, arg) => do
                       case check f `{a} arg of
                         Nothing => fail "Failed at argument of type \{show arg}"
                         Just (Left sp) => pure $ functorFun fc sp mapName funName v
                         Just (Right free) => pure v
             pure $ PatClause fc
               (apply fc (IVar fc mapName) [ fun, apply fc (IVar fc cName) vars])
               (apply fc (IVar fc cName) recs)
    logMsg "derive.functor.clauses" 1 $ joinBy "\n" ("" :: map (("  " ++) . show) cls)
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq]
        $ MkTy fc fc mapName
          `({0 a, b : Type} -> (a -> b) -> ~(IVar fc f) a -> ~(IVar fc f) b)
      , IDef fc mapName cls
      ] `(MkFunctor {f = ~(IVar fc f)} ~(IVar fc mapName))

%logging off
%logging "derive.functor.clauses" 1
list : Functor List
list = %runElab derive


test : map @{Functor.list} Prelude.reverse (words "hello world") === ["olleh", "dlrow"]
test = Refl
