{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Intermediate.Linter (lint, LintError) where

import Lib (Ident)
import Data.List ((\\))
import Language.C (NodeInfo)
import Intermediate.Imp

import Control.Lens
    ( toListOf,
      makePrisms,
      cosmos,
      traversed,
      Plated (..))
import Text.Printf (printf)

data LintError = LintError String NodeInfo deriving (Show)

type ImpProg = [Statement NodeInfo]

makePrisms ''Statement
makePrisms ''Exp

instance Plated (Statement a) where
  plate f st =
    case st of
      If p c th el ->
        If p c <$> traverse f th <*> traverse f el
      Func fd -> do
        body' <- traverse f (funBody fd)
        pure (Func fd { funBody = body' })
      _ -> pure st

instance Plated (Exp a) where
  plate f e =
    case e of
      EAnd p e1 e2 -> EAnd p <$> f e1 <*> f e2
      EOr p e1 e2 -> EOr p <$> f e1 <*> f e2
      ENot p e' -> ENot p <$> f e'
      Infix p e1 op e2 -> Infix p <$> f e1 <*> pure op <*> f e2
      _ -> pure e



globalMutLinter :: [Ident] -> FuncDecl NodeInfo -> [LintError]
globalMutLinter globVars funDecl = map (\(id',p) -> LintError (message id') p) globMuts
  where
    message :: String -> String
    message = printf "Illegal mutation of global variable (%s)"
    globMuts :: [(Ident, NodeInfo)]
    globMuts = [(id', p) | (p, Var _ id', _) <- assmts, gVar <- globVars', id' == gVar]
    localArgs :: [Ident]
    localArgs = fst <$> funArgsTys funDecl
    globVars' = globVars \\ localArgs
    assmts :: [(NodeInfo, Exp NodeInfo, Exp NodeInfo)]
    assmts = toListOf (traversed . cosmos . _Ass) (funBody funDecl)

condLinter :: FuncDecl NodeInfo -> [LintError]
condLinter funDecl = map (LintError "Conditionals not supported" . fstOfFour) ifs
  where
    ifs :: [(NodeInfo, Exp NodeInfo, [Statement NodeInfo], [Statement NodeInfo])]
    ifs = toListOf (traversed . cosmos . _If) (funBody funDecl)
    fstOfFour (a,_,_,_) = a

annotationLinter :: [Ident] -> FuncDecl NodeInfo -> [LintError]
annotationLinter globVars funDecl =
  map (\(id',p) -> LintError (printf "Undefined variable in precondition (%s)" id') p) undefVars
  where
    undefVars = [(id', p) 
                | (p, id') <- preconds,
                   arg <- map fst $ funArgsTys funDecl,
                   id' /= arg,
                   gVar <- globVars,
                   id' /= gVar
                ]
    preconds :: [(NodeInfo, Ident)]
    preconds = toListOf (traversed . cosmos . _Var) (preConditions funDecl)

voidFuncLinter :: FuncDecl NodeInfo -> [LintError]
voidFuncLinter funDecl = case returns of
  [] -> [LintError (printf "Function (%s) has no return value." (funId funDecl))
                   (position funDecl)]
  _ -> []
  where
    returns :: [(NodeInfo, Exp NodeInfo)]
    returns = toListOf (traversed . cosmos . _Return) (funBody funDecl)



lint :: ImpProg -> [LintError]
lint prog =
  concatMap (mconcat linters) [ f | (Func f@(FuncDecl{})) <- prog ]
  where
    linters :: [FuncDecl NodeInfo -> [LintError]]
    linters =
      [globalMutLinter globalVars,
        condLinter,
        voidFuncLinter,
        annotationLinter globalVars
      ]
    globalVars = [ id' | (VarDecl _ _ id' _) <- prog]

