module TypeChecking where

import Language
import Context
import HSubst

-------------------
-- Bidirectional Typechecking
-------------------

-- type-checking for Normal Forms

check :: Eq a => Context a -> Nf a -> Nf a -> ()
check gamma (NfPi s t) (NfLam b)  = check (gamma .~. s) t' b'
  where t' = outScope t
        b' = outScope b
check gamma NfSet      NfSet      = ()
check gamma NfSet      (NfPi s t) =
  let () = check gamma NfSet s in
  check (gamma .~. s) NfSet $ outScope t
check gamma ty         (NfNe ne)
  | ty == inferNe gamma ne        = ()

-- type-inference for Neutral ones

inferNe :: Eq a => Context a -> Ne a -> Nf a
inferNe gamma (NeApp v sp) = inferSp gamma (gamma `givesTypeTo` v) sp

inferSp :: Eq a => Context a -> Nf a -> Sp (Nf a) -> Nf a
inferSp gamma ty            (Sp [])        = ty
inferSp gamma ty@(NfPi s t) (Sp (hd : sp)) = inferSp gamma t' (Sp sp)
  where () = check gamma s hd
        t' = ty `appNf` hd
