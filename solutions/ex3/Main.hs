{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

-- | Cubix tutorial: Exercise 3
--
-- In this exercise, you'll learn how to construct incremental-parametric syntax definitions:
-- how to replace a language-specific node with a generic node customized to the language.
-- This is the secret of how Cubix is able to support a new language very quickly.
-- You'll also come to master sort injections.
--
-- If you haven't read the Cubix paper, **now is a good time**. 


module Main where

import Cubix.Essentials
import Cubix.Language.Parametric.Syntax

-- | We'll be deriving some sort injections in this exercise
import Cubix.Language.Parametric.Derive ( createSortInclusionType, createSortInclusionInfer )

-- | For demonstration, we create one InjF node manually. We need to include another definition for it.
import Cubix.Language.Parametric.InjF ( projF' )

------------------------------------------------------------------------------

__TODO__ :: a
__TODO__ = undefined

---------------------------------------------------------

-- | Language definition
--
-- This is @Imp3@. It's a lot like @Imp2@, except that it's fully language-specific.
-- In the rest of this exercise, we'll be replacing many of these language-specific nodes
-- with generic nodes

data ExpL
data StatementL
data VarL


data Var (e :: * -> *) l where -- Since @e@ is never used, must annotate its kind
  Var :: String -> Var e VarL

data Statement e l where
  ImpAssign :: e VarL -> e ExpL                       -> Statement e StatementL
  While     :: e ExpL -> e StatementL                 -> Statement e StatementL
  If        :: e ExpL -> e StatementL -> e StatementL -> Statement e StatementL
  BlockStmt :: e [StatementL]                         -> Statement e StatementL

data Exp e l where
  Lt     :: e ExpL -> e ExpL  -> Exp e ExpL
  Add    :: e ExpL -> e ExpL  -> Exp e ExpL
  Mul    :: e ExpL -> e ExpL  -> Exp e ExpL
  VarExp :: e VarL            -> Exp e ExpL

  NilExp  ::         Exp e ExpL
  IntExp  :: Int  -> Exp e ExpL
  BoolExp :: Bool -> Exp e ExpL


deriveAll [''Var, ''Statement, ''Exp]


type Imp3Sig = '[Var, Statement, Exp]
type Imp3 = Term Imp3Sig


--------------------------------------------------------------------------

-- | PART 1
--
-- In this part, we will replace the language-specific `Var` node with the generic `Ident` node.
-- We mostly do this for you, in preparation for you doing this yourself for the `Block` and `Assign` nodes.

-- | This definition is identical to the output of
--
-- @
-- createSortInclusionType ''IdentL ''VarL
-- @
data IdentIsVar e l where
  IdentIsVar :: e IdentL -> IdentIsVar e VarL

deriveAll [''IdentIsVar]

-- | This instance is a sort injection: It establishes that `IdentL` is a
-- __subsort__ of `VarL`. This means that every term of sort `Identl` can be treated
-- as a term of sort `VarL`. Or, in other words: there is an injective function from
-- language-generic identifiers to language-specific variables.
--
-- This definition is almost identical to the output of:
--
-- @
-- createSortInclusionInfers ''IdentL  ''VarL
-- @
instance (IdentIsVar :-<: fs, All HFunctor fs) => InjF fs IdentL VarL where
  -- injF :: Term fs IdentL -> Term fs VarL
  injF = iIdentIsVar

  -- projF :: Term fs VarL -> Maybe (Term fs IdentL)
  -- The auto-generated version would also define `projF'`, a variant
  -- of `projF` for labeled terms, which are only partially covered in
  -- this tutorial.
  projF (project -> Just (IdentIsVar n)) = Just n
  projF _                                = Nothing



-- | PART 1 TASK
--
-- Update this definition so that it excludes the removed node and includes the generic node added
-- in this section.
--
-- When you have succeeded, uncomment exampleMImp_Version1Program below. It should compile.
--type MImp3Sig_Version1 = '[Var, Statement, Exp]
type MImp3Sig_Version1 = '[Statement, Exp, Ident, IdentIsVar]

exampleMImp_Version1Program :: Term MImp3Sig_Version1 StatementL
exampleMImp_Version1Program = iImpAssign (iIdent "x") iNilExp


-- | INTERLUDE 1: SMART_CONSTRUCTOR_DETAILS
--
-- We now explain the real signature of smart constructors
--
-- A smart constructor like `iIdent` has this signature:
--
-- @
-- iIdent :: (Ident :-<: fs, InjF fs IdentL l) => String -> Term fs l
-- @
--
-- This means that you can write @iImpAssign (iIdent "x") iNilExp@, and the compiler
-- will automatically insert a use of IdentIsVar. This lets you construct terms as easily as if the syntax
-- definition had been built from the beginning
--
-- The downside is that it needs external context to infer the result type, and so,
-- e.g.: @injF . iIdent@ will never compile, because the compiler cannot deduce
-- the result type of `iIdent`.
--
-- To that end, Cubix also provides another form of smart constructor, which can also be used in pattern matching:
--
-- @
-- pattern Ident' :: (Ident :-<: fs, All HFunctor fs) => String -> Term fs IdentL
-- @
--
-- These are also generated by `deriveAll`.

-- | PART 2
--
-- We now complete the replacement of language-specific with generic nodes.
--
-- First, you'll need to familiarize yourself
-- Head over to the documentation in "Cubix.Language.Parametric.Syntax" and familiarize
-- yourself with the `Assign` and `Block` fragments. This includes both the nodes
-- with those names and the accompanying sorts such as `LhsL` and `AssignOpL`.

-- | PART 2a
-- Figure out what sort injections you'll need to replace instances of the `ImpAssign` node
-- with instances of the generic `Assign` node. Use `createSortInclusionType` to 
-- generate sort injection nodes witnessing these sort injections. Then do the same
-- to allow generic `Block` nodes to replace Imp3-specific `BlockStmt` nodes.
--
-- You will need to (1) create sort injections from
-- Imp3-specific sorts to the sorts of the children of these nodes (e.g.: `Lhs`, `BlockItemL`),
-- and (2) create sort injections from the sorts of the generic nodes to Imp3-specific sorts.
--
-- Don't forget to `deriveAll` for these generated nodes.
-- To reference generated nodes: Know that they have names like "Sort1IsSort2"
--
-- You don't need to worry about the `AssignOpL` sort right now. Can
-- you find something that has that sort?

createSortInclusionType ''StatementL ''BlockItemL
createSortInclusionType ''BlockL     ''StatementL

createSortInclusionType ''VarL    ''LhsL
createSortInclusionType ''ExpL    ''RhsL
createSortInclusionType ''AssignL ''StatementL

deriveAll [''StatementIsBlockItem, ''BlockIsStatement, ''VarIsLhs, ''ExpIsRhs, ''AssignIsStatement]

-- | PART 2b
-- Use `createSortInclusionInfers` to create sort injections (`InjF` instances)
-- corresponding to the nodes generated in part 2a.

createSortInclusionInfer ''StatementL ''BlockItemL
createSortInclusionInfer ''BlockL     ''StatementL

createSortInclusionInfer ''VarL    ''LhsL
createSortInclusionInfer ''ExpL    ''RhsL
createSortInclusionInfer ''AssignL ''StatementL


-- | PART 2c
--
-- Update `MImp3Sig` to include the `Block` and `Assign` nodes. You'll need
-- to include some auxiliary nodes as well so that they can be used; such as `ListF`
--
--
-- Also, if you want to see what's generated by Template Haskell, you can either
--
-- * Run @stack ghci@. Load this module, and type, e.g.: ":i IdentIsVar"
-- * Compile with: --ghc-options "-ddump-splices"
--type MImp3Sig = '[Var, Statement, Exp]
type MImp3Sig = '[Statement, Exp, Ident, Assign, AssignOpEquals, Block, EmptyBlockEnd,
                  ListF,
                  IdentIsVar, StatementIsBlockItem, BlockIsStatement, VarIsLhs, ExpIsRhs, AssignIsStatement]
type MImp3 = Term MImp3Sig


-- | INTERLUDE 2
--
-- A quick note on how this process works for real languages:
--
-- At this point, if Imp3 were a real language, we would define translators
-- between `Imp3` and `MImp3`. Then, assuming a third-party parser and pretty-printer
-- for the language-specific representation in Imp3, we would effectively have a parser/pretty-printer
-- for `MImp3`.
--
-- We're skipping that, both because there is no third-party parser for Imp3,
-- and because these translators are relatively unsurprising.
--
-- Ideally, at this point we'd also define a modified version of `Statement` that omits
-- `ImpAssign` and `BlockStmt`. Cubix does not yet have machinery to automate this, so we do not.
-- For the real languages, there is the property that the @translate@ function would
-- eliminate the language-specific assignment and block nodes. For Imp3, we just have to
-- manually ensure the removed nodes are not present.
--
-- For examples of this process, go to "Cubix/Language/<any language>/Parametric/Common", and look
-- at the corresponding "Types.hs" and "Trans.hs"


-- | PART 3
--

-- | PART 3a
--
-- Define a sort injection from `AssignL` to `BlockItemL`.
-- This will allow you to write transformations that run on
-- "any language where assignments may be used in blocks" and run
-- them on Imp3.
instance InjF MImp3Sig AssignL BlockItemL where
  -- injF :: MImp3 AssignL -> MImp3 BlockItemL
  --injF  = __TODO__

  -- projF :: MImp3 BlockItemL -> Maybe (MImp3 AssignL) -- actually more general, but the function
  --                                                       you write will probably also work for the
  --                                                       more general type
  --projF = __TODO__

  injF = iStatementIsBlockItem . injF
  projF x = do StatementIsBlockItem s <- project x -- Runs in the Maybe monad
               projF s


-- | PART 3b
--
-- Similarly, define a sort injection from `IdentL` to `LhsL`
instance InjF MImp3Sig IdentL LhsL where
  -- injF :: MImp3 IdentL -> MImp3 LhsL
  --injF  = __TODO__

  -- projF :: MImp3 LhsL -> Maybe (MImp3 IdentL) -- actually more general, but the function
  --                                                you write will probably also work for the
  --                                                more general type
  --projF = __TODO__

  injF = iIdentIsVar
  projF x = do VarIsLhs s <- project x -- Runs in the Maybe monad
               projF s


-- | PART 4
--
-- Write `getAssignmentsInBlock`, a function that gets a list of assignments
-- directly inside a block. It should work on C, Java, JavaScript, and Lua --- and,
-- if you completed part 3, on Imp3.
getAssignmentsInBlock :: (InjF fs AssignL BlockItemL, Block :-<: fs, ExtractF [] (Term fs), All HFoldable fs)
                      => Term fs BlockL -> [Term fs AssignL]
--getAssignmentsInBlock = __TODO__
getAssignmentsInBlock (Block' items _) = [x | Just x <- map projF $ extractF items]



-- | When you're done, uncomment this definition, and run main.
-- It should print out a list of length 1.
--
--  AST for the following program:
-- @
-- x := 1;
-- if (0 < x) {
--   y := true;
-- } else {
--   y := false;
-- }
-- @
exampleImp3Program :: MImp3 BlockL
--exampleImp3Program = __TODO__
exampleImp3Program = iBlock (insertF [
                                       iAssign (iIdent "x") AssignOpEquals' (iIntExp 1)
                                     , iIf (iLt (iIntExp 0) (iVarExp $ iIdent "x"))
                                           (iBlock (insertF [
                                                       iAssign (iIdent "y") AssignOpEquals' (iBoolExp True)
                                                     ])
                                                   EmptyBlockEnd')
                                           (iBlock (insertF [
                                                       iAssign (iIdent "y") AssignOpEquals' (iBoolExp False)
                                                     ])
                                                   EmptyBlockEnd')
                            ])
                            EmptyBlockEnd'



main :: IO ()
main = putStrLn $ show $ getAssignmentsInBlock exampleImp3Program

-- | BONUS: Try actually running `getAssignmentsInBlock` on programs in C, Java, JavaScript, and Lua.
-- Look at Part 5 of Exercise 2 as a guide.