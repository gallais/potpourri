module Functor

import Control.Monad.Either

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
data HasFunctor : TTImp -> Type

data SPosIn : (t, x : Name) -> TTImp -> Type where
  SPVar  : SPosIn t x (IVar fc x)
  SPRec  : FunIs t f -> SPosIn t x arg -> SPosIn t x (IApp fc f arg)
  SPNest : HasFunctor sp -> SPosIn t x arg -> SPosIn t x (IApp fc sp arg)
  SPPi   : FreeOf x a -> SPosIn t x b -> SPosIn t x (IPi fc rig pinfo nm a b)
  SFree  : FreeOf x a -> SPosIn t x a

data FreeOf : Name -> TTImp -> Type where
  TrustMeFO : FreeOf a x

data HasFunctor : TTImp -> Type where
  TrustMeHF : HasFunctor t

catch : Elaboration m => Elab a -> m (Maybe a)
catch elab = try (Just <$> elab) (pure Nothing)

search : Elaboration m => (ty : Type) -> m (Maybe ty)
search ty = catch $ check {expected = ty} `(%search)

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

isTypeCon : Elaboration m => Name -> m (List (Name, TTImp))
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

isType : Elaboration m => TTImp -> m IsType
isType (IVar _ n) = MkIsType n [] <$> isTypeCon n
isType (IApp _ t (IVar _ n)) = { parameterNames $= (n ::) } <$> isType t
isType t = fail "Expected a type constructor, got: \{show t}"

withParams : FC -> List Name -> TTImp -> TTImp
withParams fc params t = foldr (\ x => IPi fc M0 ImplicitArg (Just x) (Implicit fc True)) t params

hasFunctor : Elaboration m => (t : TTImp) -> m (Maybe (HasFunctor t))
hasFunctor t = catch $ do
  prf <- isType t
  ty <- check {expected = Type} $ withParams emptyFC prf.parameterNames `(Functor ~(t))
  ignore $ check {expected = ty} `(%search)
  pure TrustMeHF

data Error : Type where
  NegativeOccurence : Name -> TTImp -> Error
  NotAnApplication : TTImp -> Error
  NotAFunctor : TTImp -> Error
  NotAFunctorInItsLastArg : TTImp -> Error
  UnsupportedType : TTImp -> Error
  InvalidGoal : Error
  ConfusingReturnType : Error
  -- Contextual information
  WhenCheckingConstructor : Name -> Error -> Error
  WhenCheckingArg : TTImp -> Error -> Error

Show Error where
  show = joinBy "\n" . go [<] where

    go : SnocList String -> Error -> List String
    go acc (NegativeOccurence a ty) = acc <>> ["Negative occurence of \{show a} in \{show ty}"]
    go acc (NotAnApplication s) = acc <>> ["The type \{show s} is not an application"]
    go acc (NotAFunctor s) = acc <>> ["Couldn't find a `Functor' instance for the type constructor \{show s}"]
    go acc (NotAFunctorInItsLastArg s) = acc <>> ["Not a functor in its last argument \{show s}"]
    go acc (UnsupportedType s) = acc <>> ["Unsupported type \{show s}"]
    go acc InvalidGoal = acc <>> ["Expected a goal of the form `Functor f`"]
    go acc ConfusingReturnType = acc <>> ["Confusing telescope"]
    go acc (WhenCheckingConstructor nm err) = go (acc :< "When checking constructor \{show nm}") err
    go acc (WhenCheckingArg s err) = go (acc :< "When checking argument of type \{show s}") err

typeView : (Elaboration m, MonadError Error m) =>
           (t, x : Name) -> (ty : TTImp) -> m (Either (SPosIn t x ty) (FreeOf x ty))
typeView t x (IVar fc y) = pure $ case decEq x y of
  Yes Refl => Left SPVar
  No _ => Right TrustMeFO
typeView t x ty@(IPi fc rig pinfo nm a b) = do
  Right p <- typeView t x a
    | _ => throwError (NegativeOccurence x ty)
  Left q <- typeView t x b
    | _ => pure (Right TrustMeFO)
  pure (Left (SPPi p q))
typeView t x fa@(IApp fc f arg) = do
  chka <- typeView t x arg
  case chka of
    Left sp => do
      let Just (hd ** prf) = getFn f
         | _ => throwError (NotAnApplication f)
      case decEq t hd of
         Yes Refl => pure $ Left (SPRec prf sp)
         No diff => do
           Just prf <- hasFunctor f
             | _ => throwError (NotAFunctor f)
           pure (Left (SPNest prf sp))
    Right fo => do
      Right _ <- typeView t x f
        | _ => throwError (NotAFunctorInItsLastArg fa)
      pure (Right TrustMeFO)
typeView _ _ (IPrimVal _ _) = pure (Right TrustMeFO)
typeView _ _ (IType _) = pure (Right TrustMeFO)
typeView _ _ ty = throwError (UnsupportedType ty)

apply : FC -> TTImp -> List TTImp -> TTImp
apply fc = foldl (IApp fc)

hasRec : SPosIn t x f -> Bool
hasRec SPVar = False
hasRec (SPRec _ sp) = True
hasRec (SPNest _ sp) = hasRec sp
hasRec (SPPi _ sp) = hasRec sp
hasRec (SFree _) = False

functorFun : FC -> {f : TTImp} -> SPosIn t x f -> (rec, f : Name) -> Maybe TTImp -> TTImp
functorFun fc SPVar rec f t = apply fc (IVar fc f) (toList t)
functorFun fc (SPRec y sp) rec f t = apply fc (IVar fc rec) (functorFun fc sp rec f Nothing :: toList t)
functorFun fc (SPNest _ sp) rec f t
  = ifThenElse (hasRec sp) (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
  $ apply fc (IVar fc (UN $ Basic "map"))
    (functorFun fc sp rec f Nothing :: toList t)
functorFun fc (SPPi {rig, pinfo, nm, a} _ z) rec f (Just t)
  = let nm = fromMaybe (UN $ Basic "x") nm in
    ILam fc rig pinfo (Just nm) a (functorFun fc z rec f (Just $ IApp fc t (IVar fc nm)))
functorFun fc (SPPi {rig, pinfo, nm, a} _ z) rec f Nothing
  = let tnm = UN $ Basic "t" in
    let nm = fromMaybe (UN $ Basic "x") nm in
    ILam fc MW ExplicitArg (Just tnm) (Implicit fc False) $
    ILam fc rig pinfo (Just nm) a $
    functorFun fc z rec f (Just $ IApp fc (IVar fc tnm) (IVar fc nm))
functorFun fc (SFree y) rec f t = fromMaybe `(id) t

explicits : TTImp -> Maybe (Name, List TTImp)
explicits (IPi fc rig ExplicitArg x a b) = mapSnd (a ::) <$> explicits b
explicits (IPi fc rig pinfo x a b) = explicits b
explicits (IApp _ _ (IVar _ a)) = Just (a, [])
explicits _ = Nothing

cleanup : TTImp -> TTImp
cleanup = \case
  IVar fc n => IVar fc (dropNS n)
  t => t

namespace Functor

  derive' : (Elaboration m, MonadError Error m) =>
            {default Private vis : Visibility} ->
            {default Total treq : TotalReq} ->
            m (Functor f)
  derive' = do
    Just (IApp _ (IVar _ functor) t) <- goal
      | _ => throwError InvalidGoal
    when (`{Prelude.Interfaces.Functor} /= functor) $
      logMsg "derive.functor" 1 "Expected to derive Functor but got \{show functor}"
    logMsg "derive.functor" 1 "Deriving Functor for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.functor.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs
    let fc = emptyFC
    let mapName = UN (Basic $ "map" ++ show (dropNS f))
    cls <- for cs $ \ (cName, ty) => withError (WhenCheckingConstructor cName) $ do
             let Just (para, args) = explicits ty
                 | _ => throwError ConfusingReturnType
             logMsg "derive.functor.clauses" 10 $
                "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup) args)})"
             let funName = UN $ Basic "f"
             let fun  = IVar fc funName
             let vars = map (IVar fc . UN . Basic . ("x" ++) . show . pred)
                      $ zipWith const [1..length args] args -- fix because [1..0] is [1,0]
             recs <- for (zip vars args) $ \ (v, arg) => do
                       res <- withError (WhenCheckingArg arg) $ typeView f para arg
                       pure $ case res of
                         Left sp => functorFun fc sp mapName funName (Just v)
                         Right free => v
             pure $ PatClause fc
               (apply fc (IVar fc mapName) [ fun, apply fc (IVar fc cName) vars])
               (apply fc (IVar fc cName) recs)
    let ty = MkTy fc fc mapName $ withParams fc params $
             `({0 a, b : Type} -> (a -> b) -> ~(t) a -> ~(t) b)
    logMsg "derive.functor.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . show . mapClause cleanup) cls)
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc mapName cls
      ] `(MkFunctor {f = ~(t)} ~(IVar fc mapName))

  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           Elab (Functor f)
  derive = do
    res <- runEitherT {e = Error, m = Elab} (derive' {vis, treq})
    case res of
      Left err => fail (show err)
      Right prf => pure prf

data BigTree a
  = End a
  | Branch String (List a) (Bool -> BigTree a)
  | Rose (List (BigTree a))

Show a => Show (BigTree a) where
  show (End a) = "{\{show a}}"
  show (Branch str as k) = "\{str}: \{show as} <\{show (k True)}, \{show (k False)}>"
  show (Rose ns) = assert_total $ show ns

-- %logging "derive.functor" 10
list : Functor List
list = %runElab derive

maybe : Functor Maybe
maybe = %runElab derive

either : Functor (Either err)
either = %runElab derive

vect : Functor (Vect n)
vect = %runElab derive

%hint
bigTree : Functor BigTree
bigTree = %runElab derive
-- %logging off

test : map @{Functor.list} Prelude.reverse (words "hello world") === ["olleh", "dlrow"]
test = Refl

exampleBigTree : BigTree Nat
exampleBigTree = map (2*)
               $ Branch "top" [1..5]
               $ \ b => if b then Branch "bot" [] (const (End 1))
                        else Rose (End <$> [5..1])

record Matrix m n a where
  constructor MkMatrix
  runMatrix : Vect m (Vect n a)

-- %logging "derive.functor" 10
matrix : Functor (Matrix m n)
matrix = %runElab derive
-- %logging off

data Op : Nat -> Type where
  Neg : Op 1
  Add : Op 2

data Tm : Type -> Type where
  Var : a -> Tm a
  Call : Op n -> Vect n (Tm a) -> Tm a
  Lam : Tm (Maybe a) -> Tm a

-- %logging "derive.functor" 10
tm : Functor Tm
tm = %runElab derive
-- %logging off

data Tree : Type -> Type
data Forest : Type -> Type

data Tree : Type -> Type where
  Leaf : a -> Tree a
  Node : Forest a -> Tree a

data Forest : Type -> Type where
  Empty : Forest a
  Plant : Tree a -> Forest a -> Forest a

-- %logging "derive.functor" 10
-- for now we don't insert `assert_total` in the right places so
-- we'll say that these are covering only
%hint covering tree : Functor Tree
%hint covering forest : Functor Forest

tree = %runElab derive {treq = CoveringOnly}
forest = %runElab derive {treq = CoveringOnly}
-- %logging off

failing "Negative occurence of a"

  data NOT : Type -> Type where
    MkNOT : (a -> Void) -> NOT a

  negative : Functor NOT
  negative = %runElab derive
