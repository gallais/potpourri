{-# LANGUAGE OverloadedStrings #-}

module Claims where

import Hoare
import Data.String

instance IsString Location where fromString = MkLocation
instance IsString Logical where fromString = MkLogical

double l = Assign l (Add (Var l) (Var l))

pre1  = MkPredicate [ MapsTo "l" (Val 1) ]
prog1 = MkProgram [ double "l", double "l" ]
post1 = MkPredicate [ MapsTo "l" (Val 4) ]

claim1 = MkClaim pre1 prog1 post1


pre2 = MkPredicate
  [ MapsTo "l1" (Var "a")
  , MapsTo "l2" (Var "b")
  ]

prog2 = MkProgram
  [ Assign "l1" (Add (Var "l1") (Var "l2"))
  , Assign "l2" (Sub (Var "l1") (Var "l2"))
  , Assign "l1" (Sub (Var "l1") (Var "l2"))
  ]

post2 = MkPredicate
  [ MapsTo "l1" (Var "b")
  , MapsTo "l2" (Var "a")
  ]

claim2 = MkClaim pre2 prog2 post2
