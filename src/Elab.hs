{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, desugarDecl, elabSyn ) where
import MonadFD4
import Lang
import Subst

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado.
elab ::  MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p ((v,sty):[]) t) = do ty <- elabType sty
                                       t' <- elab' (v:env) t
                                       return $ Lam p v ty (close v t')
elab' env (SLam p ((v,sty):xs) t) = do ty <- elabType sty
                                       t' <- elab' (v:env) (SLam p xs t)
                                       return $ Lam p v ty (close v t')
elab' env (SFix p (f,sfty) ((x,sxty):[]) t) = do fty <- elabType sfty
                                                 xty <- elabType sxty
                                                 t'  <- elab' (x:f:env) t
                                                 return $ Fix p f fty x xty (close2 f x t')
elab' env (SFix p (f,sfty) ((x,sxty):xst) t) = do fty <- elabType sfty
                                                  xty <- elabType sxty
                                                  t'  <- elab' (x:f:env) (SLam p xst t)
                                                  return $ Fix p f fty x xty (close2 f x t')
elab' env (SIfZ p c t e)         = do cond <- elab' env c
                                      t1   <- elab' env t
                                      t2   <- elab' env e
                                      return $ IfZ p cond t1 t2
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do t1 <- elab' env t
                                   t2 <- elab' env u
                                   return $ BinaryOp i o t1 t2
-- Operador Print
elab' env (SPrint i str t) = do t' <- elab' env t
                                return $ Print i str t'
-- Aplicaciones generales
elab' env (SApp p h a) = do t1 <- elab' env h
                            t2 <- elab' env a
                            return $ App p t1 t2
elab' env (SLet p (v,svty) def body) = do vty <- elabType svty
                                          t1  <- elab' env def
                                          t2  <- elab' (v:env) body
                                          return $ Let p v vty t1 (close v t2)

elabType :: MonadFD4 m => STy -> m Ty
elabType SNatTy = return NatTy
elabType (SFunTy st1 st2) =  do t1 <- elabType st1
                                t2 <- elabType st2
                                return $ FunTy t1 t2
elabType (STVar v) = do s <- get
                        l <- lookupTysyn v
                        case l of
                          Nothing -> failFD4 $ "El sinónimo de tipos " ++ v ++ " no esta definido."
                          Just ty -> do{ ty' <- elabType ty ; return ty'}

desugarDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
desugarDecl (SDecl i False v [] ty t) = do t'  <- elab t
                                           ty' <- elabType ty
                                           return $ (Decl i v ty' t')
desugarDecl (SDecl i _ f [] _ _) = error ("No arguments for function: " ++ show f)
desugarDecl (SDecl i False f xs ty t) = do t' <- elab (SLam i xs t)
                                           ty' <- elabType ty
                                           return (Decl i f ty' t')
desugarDecl (SDecl i True f ((v1, t1):[]) ty t) = do t' <- elab (SFix i (f, SFunTy t1 ty) [(v1, t1)] t)
                                                     ty' <- elabType ty
                                                     return (Decl i f ty' t')
desugarDecl (SDecl i True f ((v1, t1):xs) ty t) = do t' <- elab (SLam i xs (SFix i (f, ty) [(v1, t1)] t))
                                                     ty' <- elabType ty
                                                     return (Decl i f ty' t')

elabSyn :: MonadFD4 m => SynTy -> m (Name,STy)
elabSyn (SSyn i v ty) = return (v,ty)
