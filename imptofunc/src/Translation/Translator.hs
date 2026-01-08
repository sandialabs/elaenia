module Translation.Translator where

import Lib
import qualified Data.Map as M
import qualified Imp.AST as Imp
import qualified Func.AST as Func
import qualified Imp.Parser as IP
import Func.PrettyPrinter
import Text.Parsec.Pos (SourcePos)


import Prelude hiding (pred)

instance Functor Imp.Exp where
  fmap f (Imp.Var a i)   = Imp.Var (f a) i
  fmap f (Imp.EInt a i)  = Imp.EInt (f a) i
  fmap f (Imp.EBool a b) = Imp.EBool (f a) b
  fmap f (Imp.EAnd a e1 e2) = Imp.EAnd (f a) (f <$> e1) (f <$> e2)
  fmap f (Imp.ENot a e) = Imp.ENot (f a) (f <$> e)
  fmap f (Imp.EString a s) = Imp.EString (f a) s
  fmap f (Imp.EChar a c) = Imp.EChar (f a) c
  fmap f (Imp.Infix a e1 op e2) = Imp.Infix (f a) (f <$> e1) op (f <$> e2)
  fmap f (Imp.FunCall a i args) = Imp.FunCall (f a) i ((fmap f) <$> args)

instance Functor Imp.FuncDecl where
  fmap f (Imp.FuncDecl p i argsTys retTy body) =
    Imp.FuncDecl (f p) i argsTys retTy ((fmap f) <$> body)

instance Functor Imp.Statement where
  fmap f (Imp.If a p t e) = Imp.If (f a) (f <$> p) ((fmap f) <$> t) ((fmap f) <$> e)
  fmap f (Imp.Ass a i e) = Imp.Ass (f a) i (f <$> e)
  fmap f (Imp.Return a e) = Imp.Return (f a) (f <$> e)
  fmap f (Imp.SExp a e) = Imp.SExp (f a) (f <$> e)
  fmap f (Imp.Func fun) = Imp.Func (f <$> fun)


globalEnv :: [Imp.Statement SourcePos] -> Func.TLD ()
globalEnv sts = 
  Func.FuncDecl () "env" [("x",Func.TString)] (Func.TMaybe Func.TInt) envBody
  where
    envBody = Func.ELet () "map" (buildFuncEnv vars) (Func.FuncCall () (Func.Var () "map") [Func.Var () "x"])
    vars = map varPair sts
    varPair (Imp.VarDecl _ _ id' (Imp.EInt _ n)) = (id', n)
    varPair _ = undefined
    buildFuncEnv :: [(Ident, Int)] -> Func.Exp ()
    buildFuncEnv ((id',n):binds) = funcAddMap (id', Func.EInt () n) (buildFuncEnv binds)
    buildFuncEnv [] = Func.Var () "empty"

funcAddMap :: (String,Func.Exp ()) -> Func.Exp () -> Func.Exp ()
funcAddMap (id',e) env = 
  Func.FuncCall () (Func.Var () "addMap") [Func.EString () id', e, env]



class Default a where
  dflt :: a -> Func.Exp ()

instance Default Func.FType where
  dflt Func.TInt = Func.EInt () 0
  dflt Func.TString = Func.EString () ""
  dflt Func.TBool = Func.EBool () False
  dflt (Func.TTuple (t1, t2)) = Func.ETuple () (dflt t1, dflt t2)
  dflt (Func.TMaybe _) = Func.ENothing ()

translType :: Imp.IType -> Func.FType   
translType Imp.TInt = Func.TInt
translType Imp.TString = Func.TString
translType Imp.TChar = Func.TChar
translType Imp.TBool = Func.TBool
translType (Imp.TFun args ret) = Func.TFun (map translType args) (translType ret)


translFunDecl :: Imp.FuncDecl SourcePos -> Func.TLD ()
translFunDecl fun = case isMain of
  False ->
    Func.FuncDecl
      ()
      (Imp.funId fun)
      (("env", envTy) : ((fmap . fmap) translType $ Imp.funArgsTys fun))
      (Func.TTuple ((translType $ Imp.funRetTy fun), envTy))
      body
  True ->
    Func.FuncDecl
      ()
      (Imp.funId fun)
      ((fmap . fmap) translType $ Imp.funArgsTys fun)
      (translType $ Imp.funRetTy fun)
      body
  where
    isMain = (Imp.funId fun) == "main"
    envTy = Func.TFun [Func.TString] (Func.TMaybe Func.TInt)
    localVars = 
      [id' | (Imp.VarDecl _ _ id' _) <- Imp.funBody fun] ++
      (fst <$> (Imp.funArgsTys fun))
    funRetTy = translType (Imp.funRetTy fun)
    body = case ifToEnd of
      [] -> tranlsStraightBlock isMain localVars funRetTy beforeIfs
      _  -> translAssmts localVars beforeIfs (translPaths paths)
    (beforeIfs,ifToEnd) = divideFunc (Imp.funBody fun)
    paths = translRetBlock (Imp.EBool (Imp.position fun) True) ifToEnd []
    translPaths [] = if isMain then dflt funRetTy else Func.ETuple () (dflt funRetTy, Func.Var () "env")
    translPaths ((p,ret,assmts):paths) = 
      Func.EIte () (translExp localVars p) (translAssmts localVars assmts (addEnv (translExp localVars ret))) (translPaths paths)
    addEnv e = Func.ETuple () (e, Func.Var () "env")



translAssmts :: [Ident] -> [Imp.Statement SourcePos] -> Func.Exp () -> Func.Exp ()
translAssmts _ [] ret = ret
translAssmts lVars ((Imp.VarDecl _ _ i e@(Imp.FunCall _ _ _)):assmts) ret =
  Func.ELet () "ret" (translExp lVars e)
            (Func.ELet () "env" (Func.FuncCall () (Func.Var () "snd") [(Func.Var () "ret")]) 
              (Func.ELet () i (Func.FuncCall () (Func.Var () "fst") [(Func.Var () "ret")])
                (translAssmts lVars assmts ret)))
translAssmts lVars ((Imp.VarDecl _ _ id' e):assmts) ret =
  Func.ELet () id' (translExp (id':lVars) e) (translAssmts (id':lVars) assmts ret)
translAssmts lVars ((Imp.Ass _ i (e@(Imp.FunCall _ _ _))):assmts) ret = case i `elem` lVars of
  True -> Func.ELet () "ret" (translExp lVars e)
            (Func.ELet () "env" (Func.FuncCall () (Func.Var () "snd") [(Func.Var () "ret")]) 
              (Func.ELet () i (Func.FuncCall () (Func.Var () "fst") [(Func.Var () "ret")])
                (translAssmts lVars assmts ret)))
  False -> undefined
translAssmts lVars ((Imp.SExp _ e@(Imp.FunCall _ _ _)):assmts) ret =
  Func.ELet () "env" (Func.FuncCall () (Func.Var () "snd") [(translExp lVars e)]) (translAssmts lVars assmts ret)
translAssmts lVars ((Imp.Ass _ i e):assmts) ret = case i `elem` lVars of
  True -> Func.ELet () i (translExp lVars e) (translAssmts lVars assmts ret)
  False -> Func.ELet () "env" (funcAddMap (i, (translExp lVars e)) (Func.Var () "env")) (translAssmts lVars assmts ret)
translAssmts _ (st:sts) _ = error (show st)


tranlsStraightBlock :: Bool -> [Ident] -> Func.FType -> [Imp.Statement SourcePos] -> Func.Exp ()
tranlsStraightBlock isMain localVars ty sts = case ret of
  [] -> translAssmts localVars assmts (dflt ty)
  ((Imp.Return _ e):_) -> case isMain of
    True -> case e of
      call@(Imp.FunCall _ _ _) -> Func.FuncCall () (Func.Var () "fst") [(translAssmts localVars assmts (translExp localVars e))]
      _ -> translAssmts localVars assmts (translExp localVars e)
    False -> translAssmts localVars assmts (Func.ETuple () ((translExp localVars e),Func.Var () "env"))
  where
    (assmts,ret) = span (not . isReturn) sts
    isReturn (Imp.Return _ _) = True
    isReturn _                = False




divideFunc :: [Imp.Statement a] -> ([Imp.Statement a],[Imp.Statement a])
divideFunc sts = go sts []
  where
    go :: [Imp.Statement a] -> [Imp.Statement a] -> ([Imp.Statement a],[Imp.Statement a])
    go [] stsUntilIf = (stsUntilIf,[])
    go sts@(st:rest) stsUntilIf = case st of
      (Imp.If _ _ _ _) -> (stsUntilIf,sts)
      _                 -> go rest (stsUntilIf ++ [st])


globalVarAccess :: Ident -> Func.Exp ()
globalVarAccess x = Func.FuncCall () (Func.Var () "getEnv") [Func.EString () x, Func.Var () "env"]


translExp :: [Ident] -> Imp.Exp a -> Func.Exp ()
translExp lVars (Imp.Var _ i) = case (i `elem` lVars) of
  True -> Func.Var () i
  False -> globalVarAccess i
translExp _ (Imp.EInt _ i) = Func.EInt () i
translExp _ (Imp.EString _ s) = Func.EString () s
translExp lVars (Imp.EAnd _ e1 e2) = Func.Infix () (translExp lVars e1) Func.And (translExp lVars e2)
translExp lVars (Imp.ENot _ e) = Func.ENot () (translExp lVars e)
translExp lVars (Imp.Infix _ e1 op e2) = Func.Infix () (translExp lVars e1) (translOp op) (translExp lVars e2)
translExp _ (Imp.EBool _ b) = Func.EBool () b
translExp lVars (Imp.FunCall _ i args) = case i `elem` libFunctions of
  True -> Func.FuncCall () (Func.Var () i) (map (translExp lVars) args)
  False -> Func.FuncCall () (Func.Var () i) (Func.Var () "env" : (map (translExp lVars) args))
  

translOp :: Imp.Op -> Func.Op
translOp Imp.Eq = Func.Eq
translOp Imp.Add = Func.Add
translOp Imp.Sub = Func.Sub
translOp Imp.Mul = Func.Mul
translOp Imp.Div = Func.Div


translRetBlock :: Imp.Exp SourcePos -> [Imp.Statement SourcePos] -> [Imp.Statement SourcePos] -> [(Imp.Exp SourcePos, Imp.Exp SourcePos, [Imp.Statement SourcePos])]
translRetBlock p ((Imp.Return _ ret):_) carry = [(p, ret, carry)] 
translRetBlock parentPred (st:sts) carry = case st of
  ass@(Imp.Ass _ _ _) -> translRetBlock parentPred sts (carry ++ [ass])
  (Imp.If p pred t e) -> 
    (translRetBlock (Imp.EAnd p parentPred pred) (t ++ sts) carry) ++
    (translRetBlock (Imp.EAnd p parentPred (Imp.ENot p pred)) (e ++ sts) carry)
  _                   -> translRetBlock parentPred sts carry
translRetBlock _ [] _ = undefined -- if this is reached, there is a branch without a return

isReturn :: Imp.Statement a -> Bool
isReturn (Imp.Return _ _) = True
isReturn _                = False


lib :: String
lib = "empty (x:string): maybe int = Nothing;\naddMap (x:string) (y:int) (map:(string -> maybe int)): (string -> maybe int) = (fun (z:string): maybe int -> if (x==z) then Just(y) else map(z));\ngetEnv (x:string) (map:(string -> maybe int)): int = if (map(x)==Nothing) then -1 else (fromMaybe(map(x)));\n"

libFunctions :: [Ident]
libFunctions = ["empty","addMap","getEnv","env"]


translImp :: FilePath -> IO ()
translImp path = do
  res <- IP.parseImp path
  case res of
    Left err -> error $ show err
    Right tlds -> 
      let
        impGlobVarDecls = [var | var@(Imp.VarDecl _ _ _ _) <- tlds]
        env = globalEnv (impGlobVarDecls)
        impFunDelcs = [fun | (Imp.Func fun) <- tlds]
        funcFunDecls = map translFunDecl impFunDelcs
      in
        writeFile "input-trans.func" (lib ++ (pp (env : funcFunDecls)))