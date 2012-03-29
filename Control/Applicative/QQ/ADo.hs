{-# LANGUAGE TemplateHaskell, CPP #-}

-- | Applicative do. Philippa Cowderoy's idea, some explanations due Edward
-- Kmett
--
-- Pointful version of "Language.Haskell.Meta.QQ.Idiom". Note the only
-- expression which has the bound variables in scope is the last one.
--
-- This lets you work with applicatives without the order of fields in an data
-- constructor becoming such a burden.
--
-- In a similar role as 'fail' in do notation, if match failures can be
-- expected, the result is an @Applicative f => f (Maybe a)@, rather than
-- @Applicative f => f a@, where @a@ may be partially defined.
module Control.Applicative.QQ.ADo (

    ado,
    ado'

    -- * Desugaring
    -- $desugaring

    -- * Caveats
    -- $caveats
    ) where

import Control.Applicative
import Language.Haskell.Meta (parseExp)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Control.Monad
import Data.Data (cast, gmapQ)

-- $desugaring
--
-- If you use patterns that may fail:
--
-- > foo :: Applicative f => f (Maybe T)
-- > foo = [$ado|
-- >    x:xs <- foo bar baz
-- >    Just y <- quux quaffle
-- >    T x y |]
--
-- 'ado' desugars to:
--
-- > foo = (\x y -> case (x,y) of
-- >                    (x:xs,Just y) -> Just $ T x y
-- >                    _ -> Nothing
-- >        ) <$> foo bar baz <*> quux quaffle
--
-- While 'ado'' desugars to the less safe:
--
-- > foo = (\(x:xs) (Just y) -> T x y) <$> foo bar baz <*> quux quaffle
--
-- If the simple patterns cannot fail, there is no 'Maybe' for the 'ado' quote,
-- just like 'ado'':
--
-- > newtype A = A Int
-- > foo :: Applicative f => f T
-- > foo = [$ado|
-- >    ~(x:xs) <- foo bar baz
-- >    A y <- quux quaffle
-- >    T x y |]
--
-- Becomes:
--
-- > foo = (\ ~(x:xs) (A y) -> T x y) <$> foo bar baz <*> quux quaffle

-- $caveats
--
-- Versions of Template Haskell shipped prior to GHC 7.4 are unable 
-- to reliably look up constructor names
-- just from a string: if there is a type with the same name, it will
-- return information for that instead. This means that the safe version of
-- 'ado' is prone to failure where types and values share names. It tries to
-- make a \"best guess\" in the common case that type and constructor have the
-- same name, but has nontrivial failure modes. In such cases, 'ado'' should
-- work fine: at a pinch, you can bind simple variables with it and case-match
-- on them in your last statement.
--
-- See also: <http://hackage.haskell.org/trac/ghc/ticket/4429>

-- | Usage:
--
-- > ghci> [$ado| a <- "foo"; b <- "bar"; (a,b) |]
-- > [('f','b'),('f','a'),('f','r'),('o','b'),('o','a'),('o','r'),('o','b'),('o','a'),('o','r')]
--
-- > ghci> [$ado| Just a <- [Just 1,Nothing,Just 2]; b <- "fo"; (a,b) |]
-- > [Just (1,'f'),Just (1,'o'),Nothing,Nothing,Just (2,'f'),Just (2,'o')]
--
-- Notice that the last statement is not of an applicative type, so when translating
-- from monadic do, drop the final 'return':
--
-- > (do x <- [1,2,3]; return (x + 1)) == [$ado| x <- [1,2,3]; x + 1 |]

ado :: QuasiQuoter
ado = ado'' False

-- | Variant of 'ado' that does not implicitly add a Maybe when patterns may fail:
--
-- > ghci> [$ado'| Just a <- [Just 1,Nothing,Just 2]; b <- "fo"; (a,b) |]
-- > [(1,'f'),(1,'o'),*** Exception: <interactive>:...
--
ado' :: QuasiQuoter
ado' = ado'' True

ado'' ::  Bool -> QuasiQuoter
ado'' b = QuasiQuoter { quoteExp = \str -> applicate b =<< parseDo str }

parseDo ::  (Monad m) => String -> m [Stmt]
parseDo str =
    let prefix = "do\n" in
    case parseExp $ prefix ++ str of
      Right (DoE stmts) -> return stmts
      Right a -> fail $ "ado can't handle:\n" ++ show a
      Left a -> fail a

applicate :: Bool -> [Stmt] -> ExpQ
applicate rawPatterns stmt = do
    (_:ps,f:es) <- fmap (unzip . reverse) $
            flip mapM stmt $ \s ->
            case s of
                BindS p e -> return (p,e)
                NoBindS e   -> return (WildP,e)
                LetS _ -> fail $ "LetS not supported"
                ParS _ -> fail $ "ParS not supported"

    b <- if rawPatterns then return True else null <$> filterM failingPattern ps

    f' <- if b
      then return $ LamE ps f
      else do
            xs <- mapM (const $ newName "x") ps
            return $ LamE (map VarP xs) $ CaseE (TupE (map VarE xs))
                [Match (TupP ps) (NormalB $ ConE 'Just `AppE` f) []
                ,Match WildP (NormalB $ ConE 'Nothing) []
                ]

    return $ foldl (\g e -> VarE '(<**>) `AppE` e `AppE` g)
                    (VarE 'pure `AppE` f')
                    es

failingPattern :: Pat -> Q Bool
failingPattern pat = case pat of
  LitP {} -> return True
  VarP {} -> return False
  TupP ps -> anyFailing ps
  ConP n ps -> liftM2 ((||) . not) (singleCon n) (anyFailing ps)
  InfixP p n q -> failingPattern $ ConP n [p, q]
  TildeP {} -> return False
  WildP -> return False
  RecP n fps -> failingPattern $ ConP n (map snd fps)
  ListP {} -> return True
  -- recurse on any subpatterns
  -- we do this implicitly because it avoids referring to the constructors
  -- by name, which means we can work with TH versions where they didn't
  -- exist
  _ -> fmap or . sequence $ gmapQ (mkQ (return False) failingPattern) pat
 where
  anyFailing = fmap or . mapM failingPattern
  mkQ d f x = maybe d f (cast x)

singleCon :: Name -> Q Bool
singleCon n = do
#if MIN_VERSION_template_haskell(2,7,0)
    n' <- lookupValueName (show n)
    n <- case n' of
      Just n -> return n
      Nothing -> fail $ "Data constructor " ++ show n ++ " not in scope"
#endif
    info <- reify n
    -- This covers the common case of a data type with one of the
    -- constructors being named the same as the type, but fails if there
    -- is a type Foo and a constructor Foo of a different type :(
    TyConI dec <- case info of
        DataConI _ _ tn _ -> reify tn
        -- we hope that the base of the tn is the same, but it is
        -- properly qualified
        TyConI (DataD _ _ _ cs _)
          | any ((nameBase n ==) . nameBase . conName) cs -> return info
          | otherwise -> errShadow
        TyConI (NewtypeD _ _ _ c _)
          | nameBase n == nameBase (conName c) -> return info -- eventually True
          | otherwise -> errShadow
        _ -> fail $ "ado singleCon: not a constructor: " ++ show info
    case dec of
        DataD _ _ _ [_] _ -> return True
        NewtypeD {} -> return True
        DataD _ _ _ (_:_) _ -> return False
        _ -> fail $ "ado singleCon: not a data declaration: " ++ show dec
  where
    errShadow = fail . concat $ ["ado singleCon: couldn't find data ",
        "dec for name: ", show n, ", sorry :( - try using ado' instead"]

conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c
