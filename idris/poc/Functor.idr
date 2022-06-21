module Functor

import Data.Maybe
import Data.Nat
import Data.String
import Data.Vect
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

functorFun : FC -> {f : TTImp} -> SPosIn t x f -> (rec, f : Name) -> TTImp -> TTImp
functorFun fc SPVar rec f t = IApp fc (IVar fc f) t
functorFun fc (SPTyp y) rec f t = IApp fc (IApp fc (IVar fc rec) (IVar fc f)) t
functorFun fc (SPPi {rig, pinfo, nm, a} _ z) rec f t
  = let nm = fromMaybe (UN $ Basic "x") nm in
    ILam fc rig pinfo (Just nm) a (functorFun fc z rec f (IApp fc t (IVar fc nm)))
functorFun fc (SFree y) rec f t = t

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

isTypeCon : Name -> Elab (List (Name, TTImp))
isTypeCon ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [] => fail "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => fail "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => fail "\{show ty} is ambiguous"
    cs <- getCons ty
    for cs $ \ n => do
      [(_, ty)] <- getType n
         | _ => fail "\{show n} is ambiguous"
      pure (n, ty)

record IsType where
  constructor MkIsType
  typeConstructor  : Name
  parameterNames   : List Name
  dataConstructors : List (Name, TTImp)

isType : TTImp -> Elab IsType
isType (IVar _ n) = MkIsType n [] <$> isTypeCon n
isType (IApp _ t (IVar _ n)) = { parameterNames $= (n ::) } <$> isType t
isType t = fail "Expected a type constructor, got: \{show t}"

explicits : TTImp -> Maybe (Name, List TTImp)
explicits (IPi fc rig ExplicitArg x a b) = mapSnd (a ::) <$> explicits b
explicits (IPi fc rig pinfo x a b) = explicits b
explicits (IApp _ _ (IVar _ a)) = Just (a, [])
explicits _ = Nothing

apply : FC -> TTImp -> List TTImp -> TTImp
apply fc = foldl (IApp fc)

cleanup : TTImp -> TTImp
cleanup = \case
  IVar fc n => IVar fc (dropNS n)
  t => t

namespace Functor

  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           Elab (Functor f)
  derive = do
    Just (IApp _ (IVar _ functor) t) <- goal
      | _ => fail "Invalid goal: cannot derive functor"
    when (`{Prelude.Interfaces.Functor} /= functor) $
      logMsg "derive.functor" 1 "Expected to derive Functor but got \{show functor}"
    logMsg "derive.functor" 1 "Deriving Functor for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.functor.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs
    let fc = emptyFC
    let mapName = UN (Basic $ "map" ++ show (dropNS f))
    cls <- for cs $ \ (cName, ty) => do
             let Just (para, args) = explicits ty
                 | _ => fail "Couldn't make sense of \{show cName}'s return type"
             logMsg "derive.functor.clauses" 10 $
                "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup) args)})"
             let funName = UN $ Basic "f"
             let fun  = IVar fc funName
             let vars = map (IVar fc . UN . Basic . ("x" ++) . show . pred)
                      $ zipWith const [1..length args] args -- fix because [1..0] is [1,0]
             recs <- for (zip vars args) $ \ (v, arg) => do
                       case check f para arg of
                         Nothing => fail "Failed at argument of type \{show arg} when checking \{showPrefix True (dropNS cName)}"
                         Just (Left sp) => pure $ functorFun fc sp mapName funName v
                         Just (Right free) => pure v
             pure $ PatClause fc
               (apply fc (IVar fc mapName) [ fun, apply fc (IVar fc cName) vars])
               (apply fc (IVar fc cName) recs)
    let ty = MkTy fc fc mapName
           $ foldr (\ x => IPi fc M0 ImplicitArg (Just x) (Implicit fc True))
                   `({0 a, b : Type} -> (a -> b) -> ~(t) a -> ~(t) b)
                   params
    logMsg "derive.functor.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . show . mapClause cleanup) cls)
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc mapName cls
      ] `(MkFunctor {f = ~(t)} ~(IVar fc mapName))

data BigTree a = Leaf a | Node (Nat -> BigTree a)

%logging "derive.functor" 10
list : Functor List
list = %runElab derive

maybe : Functor Maybe
maybe = %runElab derive

either : Functor (Either err)
either = %runElab derive

vect : Functor (Vect n)
vect = %runElab derive

bigTree : Functor BigTree
bigTree = %runElab derive
%logging off

test : map @{Functor.list} Prelude.reverse (words "hello world") === ["olleh", "dlrow"]
test = Refl
