{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{- HLINT ignore "Use print" -}

module Frontend.CLang where


import Intermediate.Imp
import Frontend.ACSL
import Lib
import Text.Printf (printf)
import qualified Data.Map as M
import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    runExceptT,
  )
import Control.Monad.State.Strict (StateT, MonadState, gets, modify, evalStateT)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad (zipWithM)
import Data.List (isSuffixOf)

import qualified Language.C as C
import qualified Language.C.Data.Ident as C
import Language.C.System.GCC
import System.Exit (die)

type ImpProg = [Statement C.NodeInfo]

type Env = M.Map Ident [(Ident,IType)]


newtype ImpTrans p a = ImpTrans { unTrans :: (ExceptT (TranslError p) (StateT Env IO)) a}
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadIO,
      MonadState Env,
      MonadError (TranslError p)
    )
  
type Trans = ImpTrans C.NodeInfo

translate :: ImpTrans p a -> IO (Either (TranslError p) a)
translate = flip evalStateT M.empty . runExceptT  . unTrans

insertTypDecl :: Ident -> [(Ident,IType)] -> Trans ()
insertTypDecl id' flds = modify $ M.insert id' flds

getEnvType :: C.Ident -> Trans [(Ident,IType)]
getEnvType id' = do
  res <- gets (M.lookup impId)
  case res of
    Just flds -> return flds
    Nothing -> throwError $
      TranslError (printf "type (%s) not found" impId) (C.nodeInfo id')
  where
    impId = translId id'

pShow :: C.Pretty a => a -> String
pShow = show . C.pretty


parse
  :: FilePath
  -> IO ImpProg
parse path = do
  fl <- readFile path
  (C.CTranslUnit extDecls _) <- handle $ C.parseCFile (newGCC "gcc") Nothing [] path
  prog <- handle $ translProg extDecls
  annots <- functionAnnotations extDecls fl
  return $ mergeAnnotations annots prog
  where
    translProg :: [C.CExtDecl] -> IO (Either (TranslError C.NodeInfo) ImpProg)
    translProg = translate . translImp

handle :: Show a => IO (Either a b) -> IO b
handle action = do
  e <- action
  either (die . show) pure e

functionAnnotations :: [C.CExtDecl] -> String -> IO [(Ident, [Exp C.NodeInfo])]
functionAnnotations extDecls file =
  mapM transAnot funAnots
  where
    transAnot (fn, ans) = do
      ans' <- mapM (handle . runTranslExp) ans
      pure (fn, ans')
    funAnots =  [(fn, an) |
                 (fn, fnLn) <- fnLocs,
                 (an, anLn) <- annLocs,
                 anLn == (fnLn - 1)
                ]
    fnLocs = funLocs extDecls
    annLocs = parseAcslComments file
    runTranslExp :: C.CExpr -> IO (Either (TranslError C.NodeInfo) (Exp C.NodeInfo))
    runTranslExp = translate . translExp


funLocs :: [C.CExtDecl] -> [(Ident, Int)]
funLocs tlds = [((,) <$> funId <*> lineNumber) tld |
                  tld@(C.CFDefExt (C.CFunDef {})) <- tlds]
  where
    funId :: C.CExtDecl -> Ident
    funId (C.CFDefExt (C.CFunDef _  (C.CDeclr (Just cFunId) _ _ _ _) _ _ _)) = translId cFunId
    funId _ = undefined -- will never be hit
    lineNumber :: C.Pos a => a -> Int
    lineNumber =  C.posRow . C.posOf

mergeAnnotations :: [(Ident, [Exp C.NodeInfo])] -> ImpProg -> ImpProg
mergeAnnotations anots = map annotate
  where
    anotMap = M.fromList anots
    annotate :: Statement C.NodeInfo -> Statement C.NodeInfo
    annotate st@(Func fDecl) = case M.lookup (funId fDecl) anotMap of
      Just precs -> Func $ fDecl {preConditions = precs}
      Nothing -> st
    annotate st = st



translError :: forall a n. C.CNode n => String -> n -> Trans a
translError str node = throwError $ TranslError str (C.nodeInfo node)

ppTy :: C.CTypeSpecifier a -> String
ppTy = \case
  C.CVoidType _ -> "void"
  C.CCharType _ -> "char"
  C.CShortType _ -> "short"
  C.CIntType _ -> "int"
  C.CLongType _ -> "long"
  C.CFloatType _ -> "float"
  C.CDoubleType _ -> "double"
  C.CSignedType _ -> "signed int"
  C.CUnsigType _ -> "unsigned int"
  C.CBoolType _ -> "bool"
  C.CComplexType _ -> "complex"
  C.CInt128Type _ -> "int128"
  C.CUInt128Type _ -> "uint128"
  -- [TODO] Finish this
  _              -> "type"



translType :: C.CTypeSpecifier C.NodeInfo -> Trans IType
translType = \case
  C.CVoidType _    -> return TVoid
  C.CCharType _    -> return TChar
  C.CIntType _     -> return TInt
  C.CBoolType _    -> return TBool
  C.CFloatType _   -> return TFloat
  C.CDoubleType _  -> return TDouble
  C.CTypeDef id' _ -> return $ TStruct (translId id')
  t                -> translError (printf "(%s) type unsupported" (show t)) t

translId :: C.Ident -> Ident
translId (C.Ident id' _ _) = id'

translBinOp :: C.CBinaryOp -> C.NodeInfo -> Trans Op
translBinOp op pos = case op of
  C.CMulOp -> return Mul
  C.CDivOp -> return Div
  C.CAddOp -> return Add
  C.CSubOp -> return Sub
  C.CEqOp  -> return Eq
  C.CNeqOp -> return Neq
  C.CLeqOp -> return LtEq
  C.CGrOp  -> return Gt
  C.CLeOp  -> return Lt
  op       -> throwError $ TranslError (printf "(%s) op not supported" (pShow op)) pos


translFloatString :: a -> String -> Trans (Exp a)
translFloatString a fStr = return $
  if fStr `endsWith` "f" 
    then EFloat a (init fStr)
    else EDouble a fStr
  where
    endsWith :: Eq a => [a] -> [a] -> Bool
    endsWith suffix xs = suffix `isSuffixOf` xs


translExp :: C.CExpr -> Trans (Exp C.NodeInfo)
translExp = \case
  C.CVar ident p -> return $ Var p (translId ident)
  C.CConst cnst -> case cnst of
    C.CIntConst (C.CInteger n _ _) p -> return $ EInt p (fromIntegral n)
    C.CCharConst (C.CChar c _) p     -> return $ EChar p c
    C.CFloatConst (C.CFloat f) p     -> translFloatString p f
    C.CStrConst (C.CString str _) p  -> return $ EString p str
    cnst                             -> translError (printf "(%s) constant not supported" (pShow cnst)) cnst
  cCall@(C.CCall f args p)           -> do
    f' <- translExp f
    args' <- mapM translExp args
    case f' of
      (Var _ fId) -> return $ FunCall p fId args'
      _           -> translError (printf "(%s) not a function" (pShow f)) cCall
  C.CBinary cOp ce1 ce2 p            -> do
    e1 <- translExp ce1
    e2 <- translExp ce2
    case cOp of
      C.CAndOp -> return $ EAnd p e1 e2
      C.COrOp  -> return $ EOr p e1 e2
      _        -> do
        op' <- translBinOp cOp p
        return $ Infix p e1 op' e2
  C.CMember e1 id' _ p -> do
    e1' <- translExp e1
    return $ EStructAcc p e1' (translId id')
  C.CIndex e1 e2 p -> do
    e1' <- translExp e1
    e2' <- translExp e2
    return $ ArrAcc p e1' e2'
  e -> translError (printf "(%s) expresssion not supported" (pShow e)) e

translStatement :: C.CStat -> Trans (Statement C.NodeInfo)
translStatement = \case
  C.CReturn (Just cExp) p  -> Return p <$> translExp cExp
  C.CIf cExp then' Nothing p ->
      If p <$>
         translExp cExp <*>
         (statementBlocks then' >>= translCompoundBlocks) <*>
         return []
  C.CIf cExp then' (Just else') p ->
    If p <$>
       translExp cExp <*>
       (statementBlocks then' >>= translCompoundBlocks) <*>
       (statementBlocks else' >>= translCompoundBlocks)
  C.CExpr (Just cExp) p    ->
    case cExp of
      C.CAssign cOp ce1 ce2 _ ->
        case cOp of
          C.CAssignOp -> Ass p <$> translExp ce1 <*> translExp ce2
          _           -> translError (printf "(%s) op not supported" (pShow cOp)) cExp
      _ -> SExp p <$> translExp cExp
  stmt                    ->  translError (printf "(%s) statement not supported" (pShow stmt)) stmt

statementBlocks :: C.CStat -> Trans [C.CBlockItem]
statementBlocks (C.CCompound _ blks _) = return blks
statementBlocks _                      = undefined

translCompoundBlocks :: [C.CBlockItem] -> Trans [Statement C.NodeInfo]
translCompoundBlocks = mapM go
  where
    go :: C.CBlockItem -> Trans (Statement C.NodeInfo)
    go = \case
      C.CBlockStmt stmt -> translStatement stmt
      C.CBlockDecl decl -> translDecl decl
      blk@(C.CNestedFunDef _) -> translError "Nested functions not supported" blk

translImp :: [C.CExtDecl] -> Trans ImpProg
translImp = mapM tld

tld :: C.CExtDecl -> Trans (Statement C.NodeInfo)
tld decl = case decl of
  -- Variable/Struct declaration
  C.CDeclExt declr@(C.CDecl {}) -> translDecl declr
  -- Function declaration
  C.CFDefExt funDef@(C.CFunDef {}) -> Func <$> translFunDef funDef
  extDecl         -> throwError $ TranslError "Decl not supported" (C.nodeInfo extDecl)


pattern StructTypeSpec :: [C.CDecl] -> C.NodeInfo -> C.CDeclSpec
pattern StructTypeSpec strFlds p <-
  C.CTypeSpec (C.CSUType (C.CStruct C.CStructTag Nothing (Just strFlds) [] _) p)
  

pattern VariableDecl :: C.CTypeSpec -> C.Ident -> Maybe C.CInit -> C.NodeInfo -> C.CDecl
pattern VariableDecl cTy cId cInit p <-
  C.CDecl [C.CTypeSpec cTy] [(Just (C.CDeclr (Just cId) _ _ _ _), cInit, Nothing)] p

pattern TypeDefDecl :: C.Ident ->  [C.CDecl] -> C.NodeInfo -> C.CDecl
pattern TypeDefDecl cId fieldDecls p <-
  C.CDecl [C.CStorageSpec (C.CTypedef _), StructTypeSpec fieldDecls _]
          [(Just (C.CDeclr (Just cId) _ _ _ _), _, _)]
          p


structFldsSpec :: C.CDecl -> Trans [(Ident, IType)]
structFldsSpec (C.CDecl cTys fldDeclrs _) =
    zipWithM structFldSpec
          (map fldSpec fldDeclrs)
          (map declrSpecType cTys)
  where
    structFldSpec :: (C.Ident, Maybe Integer) -> C.CTypeSpec -> Trans (Ident, IType)
    structFldSpec (id', Nothing) cTy = (,) (translId id') <$> translType cTy
    structFldSpec (id', Just size) cTy = do
      ty <- translType cTy
      return (translId id', TArray ty size)
    fldSpec :: (Maybe C.CDeclr, Maybe C.CInit, Maybe C.CExpr) -> (C.Ident, Maybe Integer)
    fldSpec (Just fldSpecs, _, _) = fldCDeclr fldSpecs
    fldSpec _ = undefined
    fldCDeclr (C.CDeclr (Just fldId) [C.CArrDeclr [] (C.CArrSize False (C.CConst (C.CIntConst size _))) _] _ _ _) =
      (fldId, Just $ C.getCInteger size)
    fldCDeclr (C.CDeclr (Just fldId) [] _ _ _) =
      (fldId, Nothing)
    fldCDeclr _ = undefined
    declrSpecType (C.CTypeSpec t) = t
    declrSpecType _ = undefined
structFldsSpec _ = undefined

translDecl :: C.CDecl -> Trans (Statement C.NodeInfo)
translDecl = \case
  VariableDecl cTy cId cInit p ->
    VarDecl p <$> translType cTy <*> pure (translId cId) <*> translInitExp cInit
  (TypeDefDecl id' fldDecls p) -> do
    fldsTys <- mapM structFldsSpec fldDecls
    let fldsTys' = concat fldsTys
    let impId = translId id'
    insertTypDecl impId fldsTys'
    return $ TypeDecl p impId fldsTys'
  decl        -> translError (printf "%s \ndeclaration not supported" (pShow decl)) decl
  where
    translInitExp :: Maybe (C.CInitializer C.NodeInfo) -> Trans (Maybe (Exp C.NodeInfo))
    translInitExp (Just (C.CInitExpr cExp _)) = Just <$> translExp cExp
    translInitExp Nothing                     = return Nothing
    translInitExp _                           = undefined



translFunDef :: C.CFunDef -> Trans (FuncDecl C.NodeInfo)
translFunDef
  (C.CFunDef [C.CTypeSpec retTy] (C.CDeclr (Just cFunId) [C.CFunDeclr funDeclr _ _] _ _ _) [] (C.CCompound _ body _) p) =
    FuncDecl p
             (translId cFunId) <$>
             argsTys <*>
             translType retTy <*>
             translCompoundBlocks body <*>
             return []
  where
    argsTys = case funDeclr of
      Right (argDeclrs, _) ->
        case argDeclrs of
        [C.CDecl [C.CTypeSpec (C.CVoidType _)] [] _] -> pure []
        _                                            ->
          mapM argTyPairs argDeclrs
      _                    -> undefined
    argTyPairs (VariableDecl cTy cId _ _) = (,) (translId cId) <$> translType cTy
    -- [TODO] Handle void type
    argTyPairs decl = error $ show decl
translFunDef def = translError "funtion definition type not supported" (C.nodeInfo def)

