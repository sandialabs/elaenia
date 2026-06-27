{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Functor law" -}
{- HLINT ignore "Use if" -}
module Intermediate.ImpToFunc (translate) where

import Lib
import qualified Intermediate.Imp as Imp
import Intermediate.Func
import Intermediate.FuncPretty (pp)
import Data.List.NonEmpty( NonEmpty(..), toList )
import Language.C (NodeInfo (..),  nopos, undefNode)
import Text.Printf (printf)

import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.Extra (ifM)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.State.Strict (StateT, MonadState, put, modify, get, gets, evalStateT)
import qualified Data.Map as M
import System.Exit (die)

import Prelude hiding (pred)
import Error (TranslError (..))
import GHC.Stack (HasCallStack)
import Data.Bifunctor (first)
import Data.List (sortOn)
import UserOptions
import Control.Monad.Reader (ReaderT (runReaderT), asks, MonadReader)

type Env = M.Map Ident FType

newtype FuncTransl p a = FuncTransl {unTrans :: ExceptT (TranslError p) (ReaderT Options (StateT Env IO)) a}
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadIO,
      MonadState Env,
      MonadReader Options,
      MonadError (TranslError p)
    )

type Trans = FuncTransl NodeInfo

translError :: String -> NodeInfo -> Trans a
translError str pos = throwError $ TranslError str pos

addBindings :: [(Ident,FType)] -> Trans ()
addBindings bnds = modify (M.union $ M.fromList bnds)

addBinding :: (Ident,FType) -> Trans ()
addBinding = addBindings . (:[])

localScope :: Trans a -> Trans a
localScope action = do
  originalSt <- get
  ret <- action
  put originalSt
  return ret

vectorWriteOptEnabled :: Trans Bool
vectorWriteOptEnabled = asks vectorWriteOpt

undefNodeInfo :: NodeInfo
undefNodeInfo = OnlyPos nopos (nopos,0)


getType :: Ident -> NodeInfo -> Trans FType
getType id' p = do
  spec <- gets $ M.lookup id'
  case spec of
    Nothing -> do
      -- env <- get
      throwError $ TranslError (printf "(%s) Type Declaration not found" id') p
    Just ty -> return ty

getTypeNoPos :: Ident -> Trans FType
getTypeNoPos id' = do
  spec <- gets $ M.lookup id'
  case spec of
    Nothing -> throwError $ TranslError (printf "(%s) Type Declaration not found" id') undefNodeInfo
    Just ty -> return ty

translType :: HasCallStack => Imp.IType -> Trans FType
translType Imp.TInt = return TInt
translType Imp.TString = return TString
translType Imp.TChar = return TChar
translType Imp.TBool = return TBool
translType Imp.TFloat = return TFloat
translType Imp.TDouble = return TDouble
translType (Imp.TStruct id') = TSyn id' <$> getTypeNoPos id'
translType (Imp.TArray iTy size) = TVector <$> translType iTy <*> pure size
translType (Imp.TFun args ret) = TFun <$> mapM translType args <*> translType ret

translOp :: Imp.Op -> Op
translOp Imp.Eq = Eq
translOp Imp.Add = Add
translOp Imp.Sub = Sub
translOp Imp.Mul = Mul
translOp Imp.Div = Div
translOp Imp.Neq = Neq
translOp Imp.LtEq = LtEq
translOp Imp.Gt = Gt
translOp Imp.Lt = Lt

-- pattern StructArrayAccess :: a -> Imp.Exp a -> Ident -> Imp.Exp a -> Imp.Exp a
-- pattern StructArrayAccess p strct fld ix <-
--   (Imp.ArrAcc p (Imp.EStructAcc _ strct fld) ix)

translExp :: Imp.Exp NodeInfo -> Trans (Exp NodeInfo)
translExp (Imp.Var p i) = do
  ty <- getType i p
  return $ Var p i ty
translExp (Imp.EInt p i) = return $ EInt p i
translExp (Imp.EString p s) = return $ EString p s
translExp (Imp.EChar p c) = return $ EChar p c
translExp (Imp.EFloat p c) = return $ EFloat p c
translExp (Imp.EDouble p c) = return $ EDouble p c
translExp (Imp.EBool p b) = return $ EBool p b
translExp (Imp.EAnd p e1 e2) =
  Infix p <$> translExp e1 <*> pure And  <*> translExp e2
translExp (Imp.EOr p e1 e2) =
  Infix p <$> translExp e1 <*> pure Or <*> translExp e2
translExp (Imp.ENot p e) = ENot p <$> translExp e
translExp (Imp.EUnOp p op e) =
  EUnOp p (translOp op) <$> translExp e
translExp e@(Imp.Infix p e1 op e2) = do
  compRel <- compoundRel e
  case compRel of
    Just compRel' -> return compRel'
    Nothing ->
      Infix p <$> translExp e1 <*> pure (translOp op) <*> translExp e2
translExp (Imp.ArrAcc p (Imp.EStructAcc _ e1 _) ix) = do
  strIdExp <- translExp e1
  case strIdExp of
    Var _ strId sTy -> do
      case vectorType sTy of
        Just elTy -> EVecRead p strId elTy <$> translExp ix
        Nothing   -> undefined
translExp (Imp.EStructAcc p e1 id') = do
  ty <- getType id' p
  undefined
  -- case ty of
    -- TVector {} -> ERecRead p <$> translExp e1 <*> pure id'
translExp (Imp.FunCall p i args) = do
  ty <- getType i p
  FuncCall p (Var p i ty) <$> mapM translExp args

compoundRel :: Imp.Exp NodeInfo -> Trans (Maybe (Exp NodeInfo))
compoundRel (Imp.Infix p (Imp.Infix _ b1 opInner e) opOutter b2)
  | Imp.isRel opOutter, Imp.isRel opOutter =
    Just <$>
      (ECompRel p <$>
        translExp b1 <*>
        return (translOp opInner) <*>
        translExp e <*>
        return (translOp opOutter)
        <*> translExp b2)
  | otherwise = return Nothing
compoundRel _ = return Nothing


translFunDecl :: HasCallStack => Imp.FuncDecl NodeInfo -> Trans (TLD NodeInfo)
translFunDecl iFun = do
  argsTys <- mapM (mapM translType) (Imp.funArgsTys iFun)
  body <- doWithAddScope argsTys (translBody $ Imp.funBody iFun)
  retTy <- translType (Imp.funRetTy iFun)
  preconds <- doWithAddScope argsTys (mapM translExp (Imp.preConditions iFun))
  addBinding (Imp.funId iFun, TFun (snd <$> argsTys) retTy)
  return $ funDecl
            (Imp.position iFun)
            (Imp.funId iFun)
            argsTys
            retTy
            body
            preconds

doWithAddScope :: [(Ident, FType)] -> Trans a -> Trans a
doWithAddScope argsTys act = localScope (addBindings argsTys >> act)


instVector :: FType -> Integer -> Exp NodeInfo
instVector ty size = EVec undefNode (replicate (fromInteger size) $ zeroExpr ty)

zeroExpr :: FType -> Exp NodeInfo
zeroExpr = \case
  TInt -> EInt undefNode 0
  TFloat -> EFloat undefNode "0.0"
  TBool -> EBool undefNode False
  _    -> undefined

translBody :: HasCallStack => [Imp.Statement NodeInfo] -> Trans (Exp NodeInfo)
translBody (st:rest) = case st of
  Imp.If {}                  -> undefined
  Imp.SExp _ _               -> undefined
  Imp.Func {}                -> undefined
  Imp.VarDecl p ty id' Nothing -> do
    ty' <- translType ty
    doWithAddScope [(id',ty')] $
      case ty' of
          -- [TODO]: unify the following two cases
        ty@(TVector fTy size) ->
          ELet p id'
                ty
                (instVector fTy size) <$>
                translBody rest
        TSyn _ ty@(TVector fTy size) ->
          ELet p id'
                ty
                (instVector fTy size) <$>
                translBody rest
        -- [TODO]: probably rething this approach
        fTy -> ELet p id'
                      fTy
                      (zeroExpr fTy) <$>
                      translBody rest
  Imp.VarDecl p ty id' (Just initE) -> do
    ty' <- translType ty
    doWithAddScope [(id',ty')] $ do
      initE' <- translExp initE
      body' <- translBody rest
      return $ ELet p id' ty' initE' body'
  st@(Imp.Ass p e1 e2) -> do
    e1' <- translExp e1
    case e1' of
      ERecRead _ id' _ -> undefined -- [TODO]
      EVecRead _ id' _ ix -> do
        ty <- getType id' p
        ifM vectorWriteOptEnabled
          (do 
            (let', rest') <- translVecWrites p id' ty (st:rest)
            rest'' <- translBody rest'
            return $ let' rest'')
          (do
            val <- translExp e2
            rest' <- translBody rest
            return (ELet p id' ty (EVecWrite p id' ty ix val) rest'))
      Var _ id' ty ->
        ELet p id' ty <$> translExp e2 <*> translBody rest
      _ -> translError (printf "illegal expression on LHS of assignment (%s)" (pp e1')) p
  Imp.Return _ e ->
    translExp e
translBody [] = undefined -- linter makes this unreachable

translVecWrites :: 
  NodeInfo -> 
  Ident ->
  FType -> 
  [Imp.Statement NodeInfo] -> 
  Trans ((Exp NodeInfo -> Exp NodeInfo), [Imp.Statement NodeInfo])
translVecWrites p id' ty sts =
  case collectVecWriteCandidates sts of
    ((Imp.Ass _ (StructArrAcc _ ix) e) :| [], rest) -> do
      val <- translExp e
      return (ELet p id' ty (EVecWrite p id' ty (EInt p ix) val), rest)
    (vwCandsNe, rest) -> do
      vwsExp <- toVecWrites p id' ty $ groupVecWrites vwCandsNe
      return (vwsExp , rest)


-- takes in a list of vector slices and returns a partially applied
-- nested let statement which accepts a let-body
toVecWrites :: NodeInfo -> Ident -> FType -> [(Int, [Imp.Exp NodeInfo])] -> Trans (Exp NodeInfo -> Exp NodeInfo)
toVecWrites p id ty slices = do
  vecWrites <- mapM fromSlice slices
  case vecWrites of
    (vw:vws) -> return $ go vws (ELet p id ty vw)
  where
    go :: [Exp NodeInfo] -> 
          (Exp NodeInfo -> Exp NodeInfo) -> 
          (Exp NodeInfo -> Exp NodeInfo)
    go [] let'       = let'
    go (vw:vws) let' = go vws (let' . ELet p id ty vw)
    fromSlice :: (Int, [Imp.Exp NodeInfo]) -> Trans (Exp NodeInfo)
    fromSlice (ix, vals) =
      EVecWrites p id ty (EInt p ix) <$> mapM translExp vals



pattern StructArrAcc :: Imp.Exp a -> Int -> Imp.Exp a
pattern StructArrAcc e1 ix <-
  StructExpArrAcc e1 (Imp.EInt _ ix)

pattern StructExpArrAcc :: Imp.Exp a -> Imp.Exp a -> Imp.Exp a
pattern StructExpArrAcc e1 ix <-
  Imp.ArrAcc _ (Imp.EStructAcc _ e1 _) ix


-- Takes in vector write grouping candidates,
-- removes duplicate writes (preserving last write),
-- sorts vector writes based on index, and groups
-- then into monotonically increasing chunks, annotating
-- each chunk with its starting index
groupVecWrites :: NonEmpty (Imp.Statement a) -> [(Int, [Imp.Exp a])]
groupVecWrites =
  (map vecWriteSlice) . groupStepwise . arrangeVecWrites . toList
  where
    vIx :: Imp.Statement a -> Int
    vIx (Imp.Ass _ (StructArrAcc _ ix) _) = ix
    vIx _ = undefined -- won't be hit if used in conjunction with collectVecWriteCandidates
    groupStepwise :: [Imp.Statement a] -> [[Imp.Statement a]]
    groupStepwise = foldr f []
      where
        f x [] = [[x]]
        f x (g@(y:_):gs)
          | vIx y == vIx x || vIx y == vIx x + 1 = (x:g):gs
          | otherwise                            = [x]:g:gs
    vecWriteSlice :: [Imp.Statement a] -> (Int, [Imp.Exp a])
    vecWriteSlice sts@(st:_) = (vIx st, expOf <$> sts)
      where
        expOf (Imp.Ass _ (StructArrAcc _ _) e) = e
        expOf _ = undefined
    vecWriteSlice [] = undefined



-- Removes duplicate writes to the same index, preserving the last write which occurs 
-- and sorts vector writes by index and 
arrangeVecWrites :: [Imp.Statement a] -> [Imp.Statement a]
arrangeVecWrites = sortOn writeIndex . keepLast
  where
    writeIndex :: Imp.Statement a -> Int
    writeIndex (Imp.Ass _ (StructArrAcc _ ix) _) = ix
    writeIndex _ = undefined
    keepLast :: Eq a => [a] -> [a]
    keepLast [] = []
    keepLast (x:xs)
      | x `elem` xs = keepLast xs
      | otherwise   = x : keepLast xs


-- Given a list of array write Assignments, collects
-- statements which assign to the same variable
-- and returns the rest of the statements
collectVecWriteCandidates :: forall a. [Imp.Statement a] -> (NonEmpty (Imp.Statement a), [Imp.Statement a])
collectVecWriteCandidates (assm@(Imp.Ass _ (StructExpArrAcc e1 ix) _) : rest) =
  if numIndex ix
    then first (assm :|) (go rest ([], rest))
    else (assm :| [], rest)
  where
    go :: [Imp.Statement a]
       -> ([Imp.Statement a], [Imp.Statement a])
       -> ([Imp.Statement a], [Imp.Statement a])
    go (assm'@(Imp.Ass _ (StructExpArrAcc e1' ix') rhs) : rest') (assms, _)
      | e1' == e1, numIndex ix', not (sameVector e1' rhs) =
        go rest' (assms ++ [assm'], rest')
    go _ acc                    = acc
    -- [TODO] swap sameVector with something like
    -- dependsDifferentIndex which analyzes whether the
    -- RHS of a write contains a reference to a different
    -- index of the same vector 
    sameVector :: Imp.Exp a -> Imp.Exp a -> Bool
    sameVector e1 (StructExpArrAcc e2 _) = e1 == e2
    sameVector _  _                      = False
    numIndex :: Imp.Exp a -> Bool
    numIndex (Imp.EInt _ _) = True
    numIndex _              = False



translTLD :: Imp.Statement NodeInfo -> Trans (TLD NodeInfo)
translTLD = \case
  Imp.VarDecl p iTy id' (Just ex) ->
    funDecl p id' [] <$>
      translType iTy <*>
      translExp ex <*>
      pure []
  Imp.VarDecl p iTy id' Nothing ->
    error $ show (iTy, id')
  Imp.TypeDecl p id' flds -> do
    tyDecl@(_,strTy') <- translStructType (id', flds)
    addBindings [tyDecl]
    return $ TLTypeSyn p id' strTy'
  Imp.Func funDecl -> translFunDecl funDecl
  tld -> error $ show tld

-- Doesn't allow for structs which reference other structs (?)
-- 

translStructType :: (Ident, [(Ident, Imp.IType)]) -> Trans (Ident, FType)
translStructType (id', flds) = case flds of
  [(_, iTy@(Imp.TArray {}))] -> (,) id' <$> translType iTy
  flds@((_,fTy):flds') -> if all ((==) fTy . snd) flds'
            then (,) id' <$> (TVector <$> translType fTy <*> pure (toInteger $ length flds))
            else (,) id' <$> (TRecord <$> (mapM . mapM) translType flds)




translate :: Options -> [Imp.Statement NodeInfo] -> IO (FuncProg NodeInfo)
translate opts prog =
  trns (mapM translTLD prog) >>= either (die . show) return
  where
    trns :: Trans a -> IO (Either (TranslError NodeInfo) a)
    trns =  flip evalStateT M.empty . flip runReaderT opts . runExceptT  . unTrans