module CEK (evalCEK) where

import Common (abort, Pos(NoPos))
import Lang
import MonadFD4
import PPrint ( ppName )
import Eval (semOp)

-- Busqueda 
lookupEnv :: Env -> Int -> Maybe Val
lookupEnv [] _ = Nothing
lookupEnv (v:_) 0 = Just v
lookupEnv (_:xs) i = lookupEnv xs (i - 1)

-- Transforma valores en términos
val2TermCEK :: Val -> TTerm
val2TermCEK (N n) = Const (NoPos, NatTy) (CNat n)
val2TermCEK (Cl (ClosFun e f t)) = t
val2TermCEK (Cl (ClosFix e f x t)) = t


evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    v <- seek t [] []
    return (val2TermCEK v)

-- Fase de búsqueda
seek ::MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek (Print _ s t) e k = seek t e ((KPrint s): k) 
seek (BinaryOp _ bop t u) e k = seek t e ((KArgOp e bop u): k)
seek (IfZ _ c t u) e k = seek c e ((KIfz e t u): k)
seek (App _ t u) e k = seek t e ((KArg e u): k)
seek (V _ (Bound i)) e k = case lookupEnv e i of
                            Nothing -> abort "Error de ejecución: variable no encontrada."
                            Just v -> destroy v k
seek (V _ (Global v)) e k = do mtm <- lookupDecl v
                               case mtm of
                                Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName v
                                Just t -> seek t e k
seek (Const _ (CNat n)) _ k = destroy (N n) k 
seek (Lam _ f fty (Sc1 t)) e k =  destroy (Cl (ClosFun e f t)) k
seek (Fix _ f fty x xty (Sc2 t)) e k = destroy (Cl (ClosFix e f x t)) k
seek (Let _ x xty t (Sc1 u)) e k = seek t e ((KLet e u): k)
seek (V _ (Free _)) _ _ = undefined


-- Fase de reducción
destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v ((KPrint s): k) = do case v of
                                N i -> do printFD4 (s ++ show i)
                                          destroy v k
                                _ -> abort "Error de tipo en runtime! : Print"
destroy v ((KArgOp e bop u): k) = seek u e ((KValOp bop v): k)
destroy (N n') ((KValOp op (N n)): k) = destroy (N (semOp op n n')) k
destroy (N 0) ((KIfz e t u): k) = seek t e k
destroy (N _) ((KIfz e t u): k) = seek u e k
destroy (Cl clos) ((KArg e t): k) = seek t e ((KClos clos):k)
destroy v ((KClos (ClosFun e _ t)): k) = seek t (v : e) k
destroy v (KClos clos@(ClosFix e _ _ t): k) = seek t (v : (Cl clos) : e) k 
destroy v ((KLet e t): k) = seek t (v:e) k
destroy v k = undefined
