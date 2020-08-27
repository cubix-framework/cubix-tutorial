{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Cubix tutorial: Exercise 4
--
-- This is where we put everything together to unleash the
-- full power of Cubix: writing an incomplete, yet believable, transformation
-- that runs on C, Java, JavaScript, Lua, and Python.
--
-- The sanitization transformation spots variables passed to a function,
-- e.g.: @foo(x, y);@, and prepends function calls that sanitize said variables,
-- changing it to @x = sanitize(x); y = sanitize(y); foo(x, y);@.
--
-- This transformation will be pretty nice, but far from production-ready.
-- For instance, a real version would only run on string variables, and perhaps
-- do some analysis so that each string is only sanitized once.
--
-- Some new concepts you'll be using in this exercise include: labeled terms
-- (including turning unlabeled into labeled terms), which are necessary to
-- use control-flow graphs; some real use of strategy combinators,
-- which let you easily create interesting traversals;
-- and the CFG-based inserter, which gives a very fancy "insert before" operation.
-- When you run your final sanitize (or try running the official solution),
-- pay attention to what it does when the function is inside a loop condition,
-- or inside the condition of a Python @elif@.
--
-- Outside of those two concepts, you'll also use Cubix's generic fragment for
-- function calls. You'll be writing a function which looks like it creates
-- a term in some common representation, but actually expands to one of many
-- different things depending on the language!

module Main where

import Cubix.Essentials
import Cubix.Language.Parametric.Syntax

import Data.Proxy ( Proxy(..) )

-- We need a tiny amount of language-specific code
import Cubix.Language.Java.Parametric.Common ( iJavaTypeArgs )

-- A few more things needed for traversals
import Control.Monad ( MonadPlus )
import Data.Comp.Multi.Strategic ( allR, isSortR, (<+) )
import Cubix.Language.Parametric.InjF ( projF' )

-- For the driver
import System.Environment ( getArgs )

------------------------------------------------------------------------------

__TODO__ :: a
__TODO__ = undefined

------------------------------------------------------------------------------
---------------------- Language-specific code --------------------------------
------------------------------------------------------------------------------

-- | In Java, all function calls have "function call attributes," even
-- if it's an empty list of type parameters. We thence add a special case for Java

class DefaultFunctionCallAttrs fs where
  defaultFunctionCallAttrs :: Term fs FunctionCallAttrsL

instance {-# OVERLAPPABLE #-} (EmptyFunctionCallAttrs :-<: fs, All HFunctor fs) => DefaultFunctionCallAttrs fs where
  defaultFunctionCallAttrs = iEmptyFunctionCallAttrs

instance {-# OVERLAPPING #-} DefaultFunctionCallAttrs MJavaSig where
  defaultFunctionCallAttrs = iJavaTypeArgs (insertF [])

------------------------------------------------------------------------------


-- | PART 0
--
-- Create the constraints stating all operations/properties
-- that a language must have in order to run the sanitization
-- transformation.
--
-- Realistically, you'll be adding things here
-- whenever the compiler tells you you need them
--
-- The reference solution uses 22 distinct constraints.
-- We've given you all the ones that we haven't discussed
-- in detail. The remaining constraints to write are all
-- either signature inclusion (`(:-<:)`) or sort injection
-- (`InjF`) constraints.
{-
type CanSanitize fs = (
    -- General constraints
    All HTraversable fs, All HFoldable fs, All HFunctor fs
  , InsertF [] (Term fs), ListF :-<: fs
  , CfgBuilder fs

    -- Misc syntax
  , Ident :-<: fs, DynCase (TermLab fs) IdentL

    -- Function constraints
  , DynCase (TermLab fs) PositionalArgExpL
  , DynCase (TermLab fs) ReceiverL
    -- Function sort injections
  , InjF fs IdentL PositionalArgExpL
    -- Assign constraints
    -- Assign sort injections
    -- Insertion constraints
  , InjF fs AssignL BlockItemL, InsertAt fs BlockItemL
  )
-}
type CanSanitize fs = (
    -- General constraints
    All HTraversable fs, All HFoldable fs, All HFunctor fs
  , InsertF [] (Term fs), ListF :-<: fs
  , CfgBuilder fs

    -- Misc syntax
  , Ident :-<: fs, DynCase (TermLab fs) IdentL

    -- Function constraints
  , FunctionCall :-<: fs, DefaultFunctionCallAttrs fs
  , FunctionArgumentList :-<: fs, PositionalArgument :-<: fs
  , DynCase (TermLab fs) PositionalArgExpL
  , DynCase (TermLab fs) ReceiverL

    -- Function sort injections
  , InjF fs FunctionCallL RhsL, InjF fs IdentL FunctionExpL, InjF fs IdentL PositionalArgExpL

    -- Assign constraints
  , Assign :-<: fs, AssignOpEquals :-<: fs

    -- Assign sort injections
  , InjF fs IdentL LhsL

    -- Insertion constraints
  , InjF fs AssignL BlockItemL, InsertAt fs BlockItemL
  )


---------------------

-- | This is the identifier of the sanitization function.
-- For each language, we assume that it's a function in global scope called "sanitize".
sanitizeIdent :: (All HFunctor fs, Ident :-<: fs, InjF fs IdentL FunctionExpL) => Term fs FunctionExpL
sanitizeIdent = iIdent "sanitize"

-- | PART 1
-- Given an identifier @n@, create the statement `n = sanitize(n);`.
--
-- Hint: With the right constraints, the result of `iAssign` will automatically
-- be cast into a `BlockItemL`.
--
-- You can start off with something simple, like something that just return "n = n;",
-- and then build up to the real thing
makeSanitizeCall :: (CanSanitize fs) => String -> Term fs BlockItemL
--makeSanitizeCall n = __TODO__
makeSanitizeCall n = iAssign (iIdent n)
                             iAssignOpEquals
                             (iFunctionCall defaultFunctionCallAttrs
                                            sanitizeIdent
                                            (iFunctionArgumentList
                                               $ insertF [iPositionalArgument $ iIdent n]))

-- | This function wraps `makeSanitizeCall` with something that generates
-- fresh labels for each node.
--
-- `TermLab` is the analogue of `Term` where each node is labeled.
makeSanitizeCallLabeled :: (CanSanitize fs, MonadAnnotater Label m) => String -> m (TermLab fs BlockItemL)
makeSanitizeCallLabeled x = annotateLabel $ makeSanitizeCall x


-- | PART 2
--
-- `insertSanitizeCall` does the actual work of creating those "s = sanitize(s);" lines.
--
-- The workhorse of this function is the CFG-based inserter, invoked through `dominatingPrependFirst`.
-- @dominatingPrependFirst targ node@ will find places in the program to insert copies of @node@
-- that ensure it will run before @targ@. So, if @targ@ is inside the condition of a loop, this
-- will insert @node@ before the loop, at the end of the loop, and before every @continue@ statement.
--
-- `dominatingPrependFirst` does not perform the insertion immediately, but
-- queues it up to be performed when `perfomCfgInsertions` is called.
--
-- There are two holes in this function. Fill them in.
insertSanitizeCall :: forall fs m. (CanSanitize fs, MonadCfgInsertion m fs BlockItemL, MonadAnnotater Label m)
                   => ProgInfo fs
                   -> TermLab fs PositionalArgExpL
                   -> m (TermLab fs PositionalArgExpL)
insertSanitizeCall progInfo t
  | Just (x :: TermLab fs IdentL) <- projF' t
  , Just (Ident n) <- project' x = do
  -- sanitizeLine <- __TODO__
  sanitizeLine <- makeSanitizeCallLabeled n
  withContainingCfgNode progInfo t $ \parentInCfg ->
      --__TODO__
      dominatingPrependFirst parentInCfg sanitizeLine
  return t
insertSanitizeCall _ t = return t


-- | PART 3
--
-- This is your first significant use of strategy combinators.
-- The descriptively-named `forEachFunctionArgument` takes a function that runs
-- on a single function argument, and lifts it to run on every subterm of an arbitrary program.
--
-- It can be split into two parts: (1) generalizing @f@ to run on terms of arbitrary sort,
-- doing nothing for terms which are not `PositionalArgExpL`'s, and (2) running that generalized
-- @f@ on all subterms of the argument.
--
-- Study the strategy combinators section of the "Cubix.Essentials" documentation for ideas.
--
-- The reference solution consists of exactly 3 function calls, and only about 30 characters.


forEachFunctionArgument :: (Monad m, CanSanitize fs)
                       => (TermLab fs PositionalArgExpL -> m (TermLab fs PositionalArgExpL))
                       -> TermLab fs l
                       -> m (TermLab fs l)
--forEachFunctionArgument = __TODO__
forEachFunctionArgument f = alltdR $ promoteR $ addFail f


-- | PART 4
--
-- And now, the finale! Complete the call to `performCfgInsertions` below to obtain the final
-- `sanitize` transformation.
--
-- Once you've done this, have a look at the driver code below. You should now
-- be able to run your transformation on arbitrary programs in C, Java, JavaScript, Lua, and Python.
sanitize :: forall fs l. (CanSanitize fs) => Term fs l -> IO (Term fs l)
sanitize prog = stripA <$> runConcurrentSupplyLabeler sanitizeInner
  where
    sanitizeInner :: (CanSanitize fs, MonadAnnotater Label m) => m (TermLab fs l)
    sanitizeInner = do
      labeledProg <- annotateLabel prog
      let progInfo = makeProgInfo labeledProg
      -- performCfgInsertions (Proxy :: Proxy BlockItemL) __TODO__ __TODO__ __TODO__
      performCfgInsertions (Proxy :: Proxy BlockItemL)
                           progInfo
                           (forEachFunctionArgument (insertSanitizeCall progInfo))
                           labeledProg



-------------------------------------------------------------------
--------------------------- Driver code ---------------------------
-------------------------------------------------------------------

runTransform :: IO (Maybe t) -> (t -> IO String) -> IO ()
runTransform mParsedFile f = do
   parsedFile <- mParsedFile
   case parsedFile of
     Nothing -> return ()
     Just t  -> do transformedT <- f t
                   putStrLn transformedT

runSanitize :: String -> FilePath -> IO ()
runSanitize "c"      filename = runTransform (parseFile @MCSig      filename) (fmap pretty . sanitize)
runSanitize "java"   filename = runTransform (parseFile @MJavaSig   filename) (fmap pretty . sanitize)
runSanitize "js"     filename = runTransform (parseFile @MJSSig     filename) (fmap pretty . sanitize)
runSanitize "lua"    filename = runTransform (parseFile @MLuaSig    filename) (fmap pretty . sanitize)
runSanitize "python" filename = runTransform (parseFile @MPythonSig filename) (fmap pretty . sanitize)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [lang, file] -> runSanitize lang file
    _            -> putStrLn $  "Usage: tut4 <lang> <filename>\n"
                             ++ "<lang> is one of: c, java, js, lua, python"