{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- | Cubix tutorial: Exercise 2
--
-- In this exercise, you'll write a small transformation with language-specific and generic parts.
-- You'll initially write it just for a toy language, Imp2, but then extend it to a real language.

module Main where

import Cubix.Essentials
import Cubix.Language.Parametric.Syntax

-- We're using a few things that aren't in Essentials
import Data.Comp.Multi.Strategy.Classification ( subterms )
import Data.List ( nub )

-- The root sorts of a few programming languages are available as `RootSort fs` and are defined as:
--import Cubix.Language.C.Parametric.Common    ( CTranslationUnitL )
--import Cubix.Language.Java.Parametric.Common ( CompilationUnitL )
--import Cubix.Language.Lua.Parametric.Common  ( LBlockL )

import Cubix.Language.C.Parametric.Common    ( CTranslationUnitL, iCConst, iCIntConst, pattern CInteger' )
import Cubix.Language.Java.Parametric.Common ( CompilationUnitL, iLit, iNull )
import Cubix.Language.Lua.Parametric.Common  ( LBlockL, iNil )

------------------------------------------------------------------------------

__TODO__ :: a
__TODO__ = undefined

---------------------------------------------------------

-- | Language definition
--
-- Take a few minutes to familiarize yourself with the language definition below.
-- We are introducing a few new concepts.
--
-- This definition uses two generic language fragments: The @Ident@ fragment
-- is self-explanatory. You will have already seen it if you did the bonus exercise
-- in the first tutorial. The @Block@ fragment is more interesting.
--
-- The @Block@ fragment represents lists of statement-like things (BlockItem's),
-- as usually found in curly braces. In Imp1 from the previous exercise, we used a binary
-- @Seq@ node instead of a list of statements. Let''s discuss how Cubix represents lists.
--
-- In Cubix, container functors such as List and Maybe are treated as ordinary tree nodes.
-- You'll need to get comfortable using the `insertF` and `extractF` functions to
-- convert between lists of terms of sort `BlockItemL` (i.e.:: @[Imp2 BlockItemL]@)
-- and terms of sort "list of BlockItemL" (i.e.: Imp2 [BlockItemL]).
--
-- In addition to the list of @BlockItem@'s, blocks have an optional second component,
-- which we'll discuss later.
--
-- Each generic node is also equipped with an informal semantics, which makes it possible
-- to program against it. The semantics of @Block@ are that it interacts with the generic
-- assignment and variable declaration nodes to delimit a scope. But you won't have to think
-- about this in the current lesson.


data ExpL


-- | Statements in Imp2 have sort @BlockItemL@, the sort
-- of things that can be included in blocks. This means
-- that the definitions of @Statement@ and @Block@ are coupled.
-- Later lessons will explain how to remove this coupling via sort injections.
--
-- Look up the definitions of `Block` and `Ident` in the docs for
-- "Cubix.Language.Parametric.Syntax"
data Statement e l where
  ImpAssign :: e IdentL -> e ExpL                     -> Statement e BlockItemL
  While     :: e ExpL -> e BlockItemL                 -> Statement e BlockItemL
  If        :: e ExpL -> e BlockItemL -> e BlockItemL -> Statement e BlockItemL
  BlockStmt :: e BlockL                               -> Statement e BlockItemL


data Exp e l where
  Lt     :: e ExpL -> e ExpL  -> Exp e ExpL
  Add    :: e ExpL -> e ExpL  -> Exp e ExpL
  Mul    :: e ExpL -> e ExpL  -> Exp e ExpL
  VarExp :: e IdentL          -> Exp e ExpL

  NilExp  ::         Exp e ExpL
  IntExp  :: Int  -> Exp e ExpL
  BoolExp :: Bool -> Exp e ExpL


deriveAll [''Statement, ''Exp]


-- | What's this? Why are we defining this pattern synonym?
--
-- The `Block` fragment is meant to represent blocks in every language. And the
-- problem with different languages is that they're....different. Instead of a
-- one-size-fits-all approach, Cubix has ways to configure the node to capture
-- the specifics of a language.
--
-- The wrinkle with `Block`'s is that, in some languages, the last part of a
-- block (the "BlockEnd") can be different from the body. And so,
-- `Block` takes a second parameter, something of sort `BlockEndL`.
--
-- Since `Imp2` only has one node of sort `BlockEndL` (namely, `EmptyBlockEnd`),
-- the second parameter to `Block` will always have the same value, and so it
-- might as well not exist for `Imp2`. This is guaranteed by the type system.
--
-- At time of writing, Lua is the only language that uses special block-ends.
-- Specifically: Lua does not have a general "return" statement; they can only
-- syntactically appear as a block end.
pattern SimpleBlock :: (Block :-<: fs, EmptyBlockEnd :-<: fs, All HFunctor fs)
                    => Term fs [BlockItemL] -- A single node representing a list of block items.
                                            -- Use @insertF [someBlockItem]@ to construct.
                                            -- This expands into @ConsF' someBlockItem NilF'@,
                                            -- from the ListF fragment (see below)
                    -> Term fs BlockL        
pattern SimpleBlock items = Block' items EmptyBlockEnd' -- This is your first time seeing a Cubix pattern synonym.
                                                        -- @Block' x y@ has type @(Block :-<: fs) => Term fs BlockL@,
                                                        -- a term of sort Block in any language that includes the generic Block fragment.
                                                        -- It's similar to @iBlock x y@, and can also be used as a pattern.
                                                        -- See interlude SMART_CONSTRUCTOR_DETAILS from later in the tutorial
                                                        -- for more details.


-- | In order to support lists of block items,
-- the signature must also include `ListF`, which
-- enables treating list nodes as ordinary AST nodes.
type Imp2Sig = '[Statement, Exp, Ident, Block, EmptyBlockEnd, ListF]

type Imp2 = Term Imp2Sig

-----------------------------------------------------------------------------

-- | EXERCISE OVERViEW
--
-- In this exercise, we are going to implement a transformation that "clears"
-- all variables in a block. For Imp2, that means that, in a block that
-- references variables "x" and "y", it will append the following code
-- to the end of the block.
--
-- @
-- x := nil;
-- y := nil;
-- @
--
-- This is going to be a very naive transformation. It will work fine for Imp2,
-- but, when applied to a real language, it will produce code that does not
-- typecheck, and will probably attempt to assign to some identifiers
-- that aren't even variables. But doing this will introduce you to several
-- more concepts needed to write multi-language transformations.



-- | PART 1
--
-- Cubix transformations, like language definitions, are a mixture
-- of language-specific and generic parts. The `MakeClearVariableStatement`,
-- which generates the "x := nil" statements seen above, will be the language
-- specific part of this variable-clearing transformation.
--
-- YOUR TASK: Create an instance of this typeclass for `Imp2Sig`
--
-- Comprehension question: Why is this class parameterized on the signature/node type `fs`?
--                         What would happen if you tried to instead parameterized it on the
--                         general node type (i.e.: write instances like
--                         `instance MakeClearVariableStatement (Term fs)`)
--                         or the sorted node type `Term fs BlockItemL`?
class MakeClearVariableStatement fs where
  makeClearVariableStatement :: String -> Term fs BlockItemL


instance MakeClearVariableStatement Imp2Sig where
  makeClearVariableStatement n = iImpAssign (iIdent n) iNilExp

-- | We now define a helper function that will influence you in part 2.
-- This definition involves some concepts we won't introduce until later,
-- so don't worry too much about it now.

-- | Naively gets a list of of all distinct identifiers in the input term.
-- Works on any language that has identifiers.
--
-- `subterms` is a bit of Cubix magic; it infers that it should get all the
-- subterms of sort `IdentL`. Don't worry too much about this implementation yet.
referencedIdents :: (All HFoldable fs, All HFunctor fs, Ident :-<: fs, DynCase (Term fs) IdentL)
                 => Term fs l -> [String]
referencedIdents t = nub $ map (\(Ident' s) -> s) $ subterms t



-- | PART 2
--
-- Cubix transformations will work on any language that satisfies
-- a given set of constraints. In this exercise, you'll define
-- the constraints for the `CanClearVariables` transformation.
--
-- You'll need to give constraints that ensure that the transformation can call
-- `referencedIdents`, `makeClearVariableStatement`, and `extractF` on terms of the language.
-- You'll also need to make sure that the `Block`, `EmptyBlockEnd`, and
-- `Ident` nodes are defined for the language. Use the `(:-<:)` operator for this.
--
-- You can complete this concurrently with parts 3/4. Your part 3 and part 4 solutions
-- won't compile if you don't give a correct solution here.
--
-- YOUR TASK: Complete the definition of `CanClearVariables`. We've given you a head-start.

--type CanClearVariables fs = (All HTraversable fs, ExtractF [] (Term fs))

type CanClearVariables fs = ( All HTraversable fs
                            , All HFoldable    fs
                            , All HFunctor     fs

                            , Ident         :-<: fs
                            , Block         :-<: fs
                            , EmptyBlockEnd :-<: fs

                            , DynCase (Term fs) IdentL

                            , MakeClearVariableStatement fs

                            , ExtractF [] (Term fs)
                            , InsertF  [] (Term fs)
                            )


-- | PART 3
--
-- In this part, you'll write a function that takes a block, and appends statements that clear each variable.
--
-- Functions you'll need: `insertF`, `extractF`, `referencedIdents`, `makeClearVariableStatement`,
-- and standard list functions.
--
-- `extractF` and `insertF` specialize to the following type signatures, useful here:
--
-- @
-- extractF :: Term fs [BlockItemL] -> [Term fs BlockItemL]
-- insertF  :: [Term fs BlockItemL] -> Term fs [BlockItemL]
-- @
--
-- The type @Term fs [BlockItemL]@ means "term of sort 'list of block items'", while
-- @[Term fs BlockItemL]@ means "list of terms of sort 'block item'".
--
-- HINT: Your function should pattern-match on `SimpleBlock`'s like this:
--
-- @
-- addClearVariableStatementsBlock (SimpleBlock items) = ...
-- @

addClearVariableStatementsBlock :: (CanClearVariables fs) => Term fs BlockL -> Term fs BlockL
addClearVariableStatementsBlock (SimpleBlock items) = SimpleBlock (insertF $ extractF items ++ clearStatements)
  where
    clearStatements = map makeClearVariableStatement $ referencedIdents items

-- | PART 4
--
-- In this part, you'll write the final transformation, which runs addClearVariableStatementsBlock
-- on every Block node, and leaves other nodes unchanged.

-- |
-- This first function lifts `addClearVariableStatementsBlock` to work on nodes of any sort.
-- It involves the term/node distinction that we haven't discussed yet,
-- so we've provided a definition for you. After finishing part 2, uncomment
-- the definition of `addClearVariableStatementsAny` below.
addClearVariableStatementsAny :: (CanClearVariables fs) => Term fs l -> Term fs l
addClearVariableStatementsAny t = case project t of -- Attempt to cast @t@ into a node of the `Block` fragment
  -- | In this branch, it's known statically that @l@ is @BlockL@.
  --   This makes it possible to use a function that returns a @BlockL@
  Just b@(Block _ _) -> addClearVariableStatementsBlock (inject b)

  -- | Branch for things that are not a block
  Nothing            -> t


-- | PART 4: TASK
-- Write the final transformation using `addClearVariableStatementsAny`
--
-- Look in the "Cubix.Essentials" documentation for appropriate traversal functions.
addClearVariableStatements :: (CanClearVariables fs) => Term fs l -> Term fs l
addClearVariableStatements = transform addClearVariableStatementsAny

-- | When you're done, you can try running your transformation
-- on the example Imp2 program

-- | AST for the following program:
-- @
-- x := 1;
-- if (0 < x) {
--   y := true;
-- } else {
--   y := false;
-- }
-- @
exampleImp2Program :: Imp2 BlockL
exampleImp2Program = SimpleBlock $ insertF [
                       (iIdent "x") `iImpAssign` (iIntExp 1)
                     , iIf (iLt (iIntExp 0) (iVarExp $ iIdent "x"))
                           (iBlockStmt $ SimpleBlock $ insertF [
                             (iIdent "y") `iImpAssign` (iBoolExp True)
                           ])
                           (iBlockStmt $ SimpleBlock $ insertF [
                             (iIdent "y") `iImpAssign` (iBoolExp False)
                           ])
                     ]

main :: IO ()
main = do putStrLn $ show $ addClearVariableStatements exampleImp2Program

          Just cProg    <- exampleCProgram
          Just javaProg <- exampleJavaProgram
          Just luaProg <- exampleLuaProgram
          putStrLn $ pretty $ addClearVariableStatements cProg
          putStrLn $ pretty $ addClearVariableStatements javaProg
          putStrLn $ pretty $ addClearVariableStatementsGen luaProg

-- | PART 5
--
-- You've defined the "Clear variables" transformation in a language-parametric style.
-- Now it's time to reap the benefits by getting it to run on Java or C. We suggest you choose
-- Java because the C AST has a more complicated representation of constants.
--
-- Customize the transformation to run on your chosen
-- language by defining an appropriate instance of `MakeClearVariableStatement`.
-- After doing so, you should be able to run `addClearVariableStatements` on
-- programs of that language. We've defined some example programs below,
-- so you can try your transformation. Use the `pretty` function to view the results.
--
-- You'll probably write your instance to generate statements like "x = 0;" or "x = null;".
-- The generated code usually won't compile. It's okay. This is Exercise 2.
--
-- To write the instance, you'll need to learn a little bit about the language's syntax definition.
-- Start off by chasing down the definition of that language's signature, which gives
-- a list of all language fragments in that language.
--
-- E.g.: `MJavaSig` is defined
--
-- @
-- type MJavaSig = '[Annotation, ArrayIndex, ArrayInit, ...]
-- @
--
-- The language-specific nodes are given in alphabetical order at the beginning,
-- and the language-generic nodes are given at the end.
--
-- Each language's AST definition is directly based on a that of a third-party library, which defines
-- it as a traditional mutually-recursive algebraic data type. You may find these definitions
-- easier to read that the Cubix modular definitions.
--
-- Some convenience links for you:
--    * https://hackage.haskell.org/package/language-c-0.10.0/docs/Language-C-Syntax-AST.html
--    * https://hackage.haskell.org/package/language-java-0.2.9/docs/Language-Java-Syntax.html
--
-- In each case, as each of these languages use the generic `Assign` node, you'll likely want to use the `iAssign
-- smart constructor. You might notice that `Assign` nodes have sort `AssignL`, while `makeClearVariableStatement`
-- must return a node of sort `BlockItemL`. However, `iAssign` will automatically create extra nodes to convert an
-- `Assign` node into a `BlockItemL`. This is part of the magic of sort injections.
--
-- Other tips:
--
-- * Import a language like this: `import qualified Cubix.Language.Java.Parametric.Common as J`. 
--   Different syntaxes use similar or identical names for their own types and constructors
--
-- Other languages:
--  * You can try the transformation on JavaScript too, but it may not behave the way you expect,
--    as Cubix does not consider all sets of curly braces in JS to be "blocks,"
--    due to the way scopes work in JavaScript. Similar is true of Python.
--  * Lua, as discussed above, uses non-empty block-ends, so you'll get a type error if you
--    try to run on Lua, because it is missing `EmptyBlockEnd`. But, with a small change to the
--    transformation, you can remove this restriction. This is the bonus exercise below.
--
-- Documentation for the underlying JavaScript and Python grammars:
-- 
--    * https://hackage.haskell.org/package/language-javascript-0.7.1.0/docs/Language-JavaScript-Parser-AST.html
--        -- Note: language-javascript has definitions full of JSAnnot fields. The Cubix version of the syntax removes these.
--    * https://hackage.haskell.org/package/language-python-0.5.8/docs/Language-Python-Common-AST.html

exampleCProgram :: IO (Maybe (MCTerm CTranslationUnitL))
exampleCProgram = parseFile @MCSig "input-files/c/Foo.c"

exampleJavaProgram :: IO (Maybe (MJavaTerm CompilationUnitL))
exampleJavaProgram = parseFile @MJavaSig "input-files/java/Foo.java"


instance MakeClearVariableStatement MCSig where
  makeClearVariableStatement s = iAssign (iIdent s) iAssignOpEquals (iCConst $ iCIntConst (CInteger' 0) iUnitF)

instance MakeClearVariableStatement MJavaSig where
  makeClearVariableStatement s = iAssign (iIdent s) iAssignOpEquals (iLit iNull)


-- | BONUS: Generalize `addClearVariableStatementsBlock` and `CanClearVariables`
--   to be agnostic to kind of BlockEnd in the language. Then get the transformation to run on Lua.
--
--   Documentation for underlying Lua grammar:
--    * https://hackage.haskell.org/package/language-lua-0.11.0.2/docs/Language-Lua-Syntax.html


exampleLuaProgram :: IO (Maybe (MLuaTerm LBlockL))
exampleLuaProgram = parseFile @MLuaSig "input-files/lua/Foo.lua"

-- Hints about supporting Lua:
-- Remove the requirement to have EmptyBlockEnd.
-- Use Block' to create BlockItems, instead of SimpleBlock. Preserve the BlockEndL values.


instance MakeClearVariableStatement MLuaSig where
  makeClearVariableStatement name = iAssign (iIdent name) iAssignOpEquals iNil -- This `iNil` comes from Lua.

type CanClearVariablesGen fs = ( All HTraversable fs
                            , All HFoldable    fs
                            , All HFunctor     fs

                            , Ident         :-<: fs
                            , Block         :-<: fs

                            , DynCase (Term fs) IdentL
                            , MakeClearVariableStatement fs

                            , ExtractF [] (Term fs)
                            , InsertF  [] (Term fs)
                            )

-- Define versions of addClearVariableStatement* functions but with support of general BlockEnd terms.

addClearVariableStatementsBlockGen :: (CanClearVariablesGen fs) => Term fs BlockL -> Term fs BlockL
addClearVariableStatementsBlockGen (Block' items blockEnd) = Block' (insertF $ extractF items ++ clearStatements) blockEnd
  where
    clearStatements = map makeClearVariableStatement $ referencedIdents items

addClearVariableStatementsAnyGen :: (CanClearVariablesGen fs) => Term fs l -> Term fs l
addClearVariableStatementsAnyGen t = case project t of -- Attempt to cast @t@ into a node of the `Block` fragment
  -- \| In this branch, it's known statically that @l@ is @BlockL@.
  --   This makes it possible to use a function that returns a @BlockL@
  Just b@(Block _ _) -> addClearVariableStatementsBlockGen (inject b)
  -- \| Branch for things that are not a block
  Nothing -> t

addClearVariableStatementsGen :: (CanClearVariablesGen fs) => Term fs l -> Term fs l
addClearVariableStatementsGen = transform addClearVariableStatementsAnyGen
