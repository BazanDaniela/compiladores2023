{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, tysynOrElse, tysyn) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> do {x <- identifier ; return $ STVar x}
         <|> parens typeP

typeP :: P STy
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom

binders :: P [(Name,STy)]
binders = try (do
            x <- parens binding
            xs <- binders
            return (x:xs))
            <|>
            return []

tybinds :: [(Name,STy)] -> STy -> STy
tybinds [] ty     = ty
tybinds (x:xs) ty = SFunTy (snd x) (tybinds xs ty)

const :: P Const
const = CNat <$> num

printOpApp :: P STerm
printOpApp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

printOpNoApp :: P STerm
printOpNoApp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SLam i [("x",SNatTy)] (SPrint i str (SV i "x")))

printOp :: P STerm
printOp = try printOpApp <|> printOpNoApp

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, STy)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         xs <- binders
         reservedOp "->"
         t <- expr
         return (SLam i xs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         xs       <- binders
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) xs t)

letcorexp :: P STerm
letcorexp = do
  i <- getPos
  reserved "let"
  (v,ty) <- (parens binding <|> binding)
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i (v,ty) def body)

letfexp :: P STerm
letfexp = do i <- getPos
             reserved "let"
             f <- var
             (v1,t1) <- parens binding
             xs       <- binders
             reservedOp ":"
             ty <- typeP
             reservedOp "="
             t <- expr
             reserved "in"
             t' <- expr
             return (SLet i (f,tybinds ((v1,t1):xs) ty)(SLam i ((v1,t1):xs) t) t')

letrecexp :: P STerm
letrecexp = do i <- getPos
               reserved "let"
               reserved "rec"
               f <- var
               (v1,t1) <- parens binding
               xs       <- binders
               reservedOp ":"
               ty <- typeP
               reservedOp "="
               t <- expr
               reserved "in"
               t' <- expr
               case xs of
                []  -> return (SLet i (f,SFunTy t1 ty)(SFix i (f, SFunTy t1 ty) [(v1,t1)] t) t')
                xts -> return (SLet i (f,tybinds ((v1,t1):xs) ty)(SLam i xts (SFix i (f,tybinds ((v1,t1):xs) ty) xs t)) t')

letexp :: P STerm
letexp = (try letrecexp) <|> (try letcorexp) <|> letfexp

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parser de declaraciones
decl :: P (SDecl STerm)
decl = (try declVar) <|> (try declFun) <|> declRec

-- Parser declaraciones azucaradas
declVar :: P (SDecl STerm)
declVar = do
     i <- getPos
     reserved "let"
     (v, ty) <- parens binding <|> binding
     reservedOp "="
     t <- expr
     return (SDecl i False v [] ty t)

declFun :: P (SDecl STerm)
declFun = do
     i <- getPos
     reserved "let"
     f <- var
     xs <- binders
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     t <- expr
     return (SDecl i False f xs (tybinds xs ty) t)

declRec :: P (SDecl STerm)
declRec = do
     i <- getPos
     reserved "let"
     reserved "rec"
     f <- var
     xs <- binders
     reservedOp ":"
     ty <- typeP
     reservedOp "="
     t <- expr
     return (SDecl i True f xs (tybinds xs ty) t)

tysyn :: P SynTy
tysyn = do i <- getPos
           reserved "type"
           v <- var
           reservedOp "="
           t <- typeP
           return (SSyn i v t)

-- | Parser de programas (listas de declaraciones)
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm = try (Left <$> decl) <|> (Right <$> expr)

tysynOrElse :: P (Either (Either (SDecl STerm) STerm) SynTy)
tysynOrElse = try (Left <$> declOrTm) <|> (Right <$> tysyn)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
