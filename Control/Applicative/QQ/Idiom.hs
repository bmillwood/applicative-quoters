{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}

-- | Idiom brackets. Vixey's idea.

module Control.Applicative.QQ.Idiom (i) where

import Control.Applicative ((<*>), pure)
import Control.Monad ((<=<))
import Language.Haskell.Meta (parseExp)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

-- ghci> [$i| (,) "foo" "bar" |]
-- [('f','b'),('f','a'),('f','r'),('o','b'),('o','a'),('o','r'),('o','b'),('o','a'),('o','r')]
i :: QuasiQuoter
i = QuasiQuoter { quoteExp = applicate <=< either fail return . parseExp }

applicate :: Exp -> ExpQ
applicate (AppE f x) =
  [| $(applicate f) <*> $(return x) |]
applicate (InfixE (Just left) op (Just right)) =
  [| pure $(return op) <*> $(return left) <*> $(return right) |]
applicate (UInfixE left op right) = case (left,right) of
  (UInfixE{}, _) -> ambig
  (_, UInfixE{}) -> ambig
  (_, _) -> [| pure $(return op) <*> $(return left) <*> $(return right) |]
 where
  ambig = fail "Ambiguous infix expression in idiom bracket."
applicate x = [| pure $(return x) |]

