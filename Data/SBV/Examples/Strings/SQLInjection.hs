-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.SQLInjection
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- This implements the symbolic evaluation of a language which operates on
-- strings in a way similar to bash. It's possible to do different analyses,
-- but this example finds program inputs which result in a query containing a
-- SQL injection.
--
-- The example program (in pseudo-code) @query ("SELECT msg FROM msgs where
-- topicid='" ++ my_topicid ++ "'")@ can be analyzed via:
--
-- >>> findInjection exampleProgram
-- Satisfiable. Model:
-- my_topicid = "h'; DROP TABLE 'users" :: String
-- undef      =                      "" :: String
-- s2         =                      "" :: String
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Strings.SQLInjection
  ( findInjection
  , exampleProgram
  ) where

import Control.Monad.State
import Control.Monad.Writer
import Data.SBV hiding (name)
import Data.String

data Expr
  = Query Expr
  | Const String
  | Concat Expr Expr
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
  ReadVar nameExp -> do
    name <- eval nameExp
    arr <- get
    pure $ readArray arr name
  WriteVar nameExp valExp -> do
    name <- eval nameExp
    val  <- eval valExp
    modify $ \arr -> writeArray arr name val
    pure val

-- | A simple program to query all messages with a given topic id.
exampleProgram :: Expr
exampleProgram = Query
  (Concat
    (Concat
      "SELECT msg FROM msgs WHERE topicid='"
      (ReadVar "my_topicid"))
    "'")

nameRe, strRe, selectRe, dropRe, statementRe, exploitRe :: SRegExp

-- we have to severely limit the length of names and strings to get an answer
nameRe = RE_Loop 1 7 (RE_Range 'a' 'z')
strRe = "'" * RE_Loop 1 5 (RE_Range 'a' 'z' + " ") * "'"

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
  * "DROP TABLE 'users'"

-- | Analyze the program for inputs which result in a SQL injection. There are
-- other possible injections, but in this example we're only looking for a
-- @DROP TABLE@ command.
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
