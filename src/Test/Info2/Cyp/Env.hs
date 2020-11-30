module Test.Info2.Cyp.Env
    ( declEnv
    , generalizeEnv
    , generalizeEnvProp
    , interpretProp
    , interpretTerm
    , declareTerm
    , declareProp
    , variantFixes
    , variantFixesTerm
    )
where

import qualified Data.Map.Strict as M

import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types

-- Environment to interpret declaration terms in ...
-- Not a real environment
declEnv :: Env
declEnv = Env { datatypes = [], axioms = [], constants = [], fixes = M.empty, goals = [] }

interpretTerm :: Env -> RawTerm -> Term
interpretTerm env = fmap f
  where
    f v = case M.lookup v (fixes env) of
        Nothing -> (v, 0)
        Just n -> (v, n)

interpretProp :: Env -> RawProp -> Prop
interpretProp env = propMap (interpretTerm env)

variantFixes :: [String] -> Env ->  ([IdxName], Env)
variantFixes xs env = (xs', env')
  where
    ins free = M.insertWith (\_ n -> n + 1) free 0
    fixes' = foldl (flip ins) (fixes env) xs
    env' = env { fixes = fixes' }
    xs' = map (\x -> (x, M.findWithDefault 0 x fixes')) xs

variantFixesTerm :: RawTerm -> Env -> (Term, Env)
variantFixesTerm rt env = (interpretTerm env' rt, env')
  where
    (_, env') = variantFixes (collectFrees rt []) env

declareTerm :: RawTerm -> Env -> (Term, Env)
declareTerm rt env = (interpretTerm env' rt, env')
  where
    ins free = M.insertWith (\_ n -> n) free 0
    fixes' = foldl (flip ins) (fixes env) $ collectFrees rt []
    env' = env { fixes = fixes' }

declareProp :: RawProp -> Env -> (Prop, Env)
declareProp rprop@(Prop l r) env = (prop, env'')
  where
    (_, env') = declareTerm l env
    (_, env'') = declareTerm r env'
    prop = propMap (interpretTerm env'') rprop

generalizeEnv :: Env -> Term -> Term
generalizeEnv env = generalizeExcept (M.toList (fixes env))

generalizeEnvProp :: Env -> Prop -> Prop
generalizeEnvProp env = generalizeExceptProp (M.toList (fixes env))
