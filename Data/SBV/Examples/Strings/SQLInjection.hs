{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Strings.SQLInjection
  ( findInjection
  , exampleProgram
  ) where

import Control.Monad.State
import Control.Monad.Writer
import Data.String
import Data.SBV hiding (name)

data Expr
  = Query Expr
  | Const String
  | Concat Expr Expr
  | Interpolate [Expr] Expr
  | ReadVar Expr
  | WriteVar Expr Expr

instance IsString Expr where
  fromString = Const

type M = StateT (SFunArray String String) (WriterT [SString] Symbolic)

-- TODO: this is only interesting with ite
eval :: Expr -> M (SBV String)
eval expr = case expr of
  Query q -> do
    q' <- eval q
    tell [q']
    lift $ lift exists_
  Const str -> pure $ literal str
  Concat exp1 exp2 -> (.++) <$> eval exp1 <*> eval exp2
  Interpolate varnames template -> do
    varnames' <- traverse eval varnames
    template' <- eval template
    foldM
      (\tmpl name -> do
        arr <- get
        let val = readArray arr name
        pure $ strReplace tmpl name val
      )
      template' varnames'
  ReadVar nameExp -> do
    name <- eval nameExp
    arr <- get
    pure $ readArray arr name
  WriteVar nameExp valExp -> do
    name <- eval nameExp
    val  <- eval valExp
    modify $ \arr -> writeArray arr name val
    pure val

exampleProgram :: Expr
exampleProgram = Query
  (Concat "SELECT msg FROM messages WHERE topicid=" (ReadVar "my_topicid"))

nameRe, strRe, selectRe, dropRe, statementRe, exploitRe :: SRegExp

-- let's say names are up to 10 characters long and strings are up to 40
nameRe = RE_Loop 1 10 (RE_Range 'a' 'z' + RE_Range 'A' 'Z')
strRe = "'" * RE_Loop 1 40 (RE_Range 'a' 'z' + RE_Range 'A' 'Z' + " ") * "'"

selectRe
  = "SELECT "
  * (nameRe + "*")
  * " FROM "
  * nameRe
  * RE_Opt (
    " WHERE "
    * nameRe
    * "="
    * (nameRe + strRe)
    )

dropRe = "DROP TABLE " * (nameRe + strRe)

-- we'll simplify and say a command is just a sequence of select / drop.
statementRe = selectRe + dropRe

-- we're looking for a DROP TABLE after at least one legitimate command
exploitRe
  = RE_Plus (statementRe * "; ")
  * dropRe
  -- This runs faster if we exclude the option of trailing legitimate
  -- statements
  -- * RE_Star ("; " + statementRe)

findInjection :: Expr -> IO ()
findInjection expr = do
  satResult <- sat $ do
    my_topicid <- sString "my_topicid"
    undef      <- sString "undef"
    let env :: SFunArray String String
        env = mkSFunArray $ \varName ->
          ite (varName .== "my_topicid") my_topicid undef
    (_evalResult, queries) <- runWriterT (evalStateT (eval expr) env)
    pure $ bAny (`strMatch` exploitRe) queries

  print satResult
