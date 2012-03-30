{-# LANGUAGE TemplateHaskell #-}
-- This stuff has to be in a separate module because of the stage restriction.
module Magic where

import Language.Haskell.TH

-- | 'return's 'Just (VarE n)' if 'n' names a variable in scope, or
-- 'Nothing' if 'n' is not in scope or is not a variable.
findVar :: Name -> Q (Maybe Exp)
findVar name = recover (return Nothing) $ do
  VarI n _ _ _ <- reify name
  return (Just (VarE n))

-- | Returns a Q Exp which expands to Just lookupValueName if lookupValueName
-- exists, or Nothing if it doesn't.
maybeLookupValueName :: Q Exp
maybeLookupValueName = findVar (mkName "lookupValueName") >>= \e -> case e of
  Nothing -> [| Nothing |]
  Just expr -> [| Just $(return expr) |]
