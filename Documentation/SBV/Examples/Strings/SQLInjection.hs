-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Puzzles.SQLInjection
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implement the symbolic evaluation of a language which operates on
-- strings in a way similar to bash. It's possible to do different analyses,
-- but this example finds program inputs which result in a query containing a
-- SQL injection.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Documentation.SBV.Examples.Strings.SQLInjection where

import Control.Monad.State
import Control.Monad.Writer
import Data.String

import Data.SBV
import Data.SBV.Control

import qualified Data.SBV.RegExp as R

-- | Simple expression language
data SQLExpr = Query   SQLExpr
             | Const   String
             | Concat  SQLExpr SQLExpr
             | ReadVar SQLExpr

-- | Literals strings can be lifted to be constant programs
instance IsString SQLExpr where
  fromString = Const

-- | Evaluation monad. The state argument is the environment to store
-- variables as we evaluate.
type M = StateT (SFunArray String String) (WriterT [SString] Symbolic)

-- | Given an expression, symbolically evaluate it
eval :: SQLExpr -> M SString
eval (Query q)         = do q' <- eval q
                            tell [q']
                            lift $ lift exists_
eval (Const str)       = return $ literal str
eval (Concat e1 e2)    = (.++) <$> eval e1 <*> eval e2
eval (ReadVar nm)      = do n   <- eval nm
                            arr <- get
                            return $ readArray arr n

-- | A simple program to query all messages with a given topic id. In SQL like notation:
--
-- @
--   query ("SELECT msg FROM msgs where topicid='" ++ my_topicid ++ "'")
-- @
exampleProgram :: SQLExpr
exampleProgram = Query $ foldr1 Concat [ "SELECT msg FROM msgs WHERE topicid='"
                                       , ReadVar "my_topicid"
                                       , "'"
                                       ]

-- | Limit names to be at most 7 chars long, with simple letters.
nameRe :: R.RegExp
nameRe = R.Loop 1 7 (R.Range 'a' 'z')

-- | Strings: Again, at most of lenght 5, surrounded by quotes.
strRe :: R.RegExp
strRe = "'" * R.Loop 1 5 (R.Range 'a' 'z' + " ") * "'"

-- | A "select" command:
selectRe :: R.RegExp
selectRe = "SELECT "
         * (nameRe + "*")
         * " FROM "
         * nameRe
         * R.Opt (  " WHERE "
                  * nameRe
                  * "="
                  * (nameRe + strRe)
                  )

-- | A "drop" instruction, which can be exploited!
dropRe :: R.RegExp
dropRe = "DROP TABLE " * (nameRe + strRe)

-- | We'll greatly simplify here and say a statement is either a select or a drop:
statementRe :: R.RegExp
statementRe = selectRe + dropRe

-- | The exploit: We're looking for a DROP TABLE after at least one legitimate command.
exploitRe :: R.RegExp
exploitRe = R.KPlus (statementRe * "; ")
          * "DROP TABLE 'users'"

-- | Analyze the program for inputs which result in a SQL injection. There are
-- other possible injections, but in this example we're only looking for a
-- @DROP TABLE@ command.
--
-- Remember that our example program (in pseudo-code) is:
--
-- @
--   query ("SELECT msg FROM msgs where topicid='" ++ my_topicid ++ "'")
-- @
--
-- We have:
--
-- >>> findInjection exampleProgram
-- "h'; DROP TABLE 'users"
--
-- Indeed, if we substitute the suggested string, we get the program:
--
-- @
--   query ("SELECT msg FROM msgs where topicid='h'; DROP TABLE 'users'")
-- @
--
-- which would query for topic 'h' and then delete the users table!
findInjection :: SQLExpr -> IO String
findInjection expr = runSMT $ do
    badTopic <- sString "badTopic"

    -- Create an initial environment that returns the symbolic
    -- value my_topicid only, and unspecified for all other variables
    emptyEnv :: SFunArray String String <- newArray "emptyEnv" Nothing

    let env = writeArray emptyEnv "my_topicid" badTopic

    (_, queries) <- runWriterT (evalStateT (eval expr) env)

    -- For all the queries thus generated, ask that one of them be "explotiable"
    constrain $ bAny (`R.match` exploitRe) queries

    query $ do cs <- checkSat
               case cs of
                 Unk   -> error "Solver returned unknown!"
                 Unsat -> error "No exploits are found"
                 Sat   -> getValue badTopic
