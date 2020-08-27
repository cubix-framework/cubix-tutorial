These are the exercises accompanying the Cubix tutorial. They are found in the `tutorial` folder.

* Exercise 1: Language fragments: Creating a toy language using the style of representation used by Cubix
* Exercise 2: Parametric syntax: Writing a small transformation that runs on multiple languages
* Exercise 3: Incremental parametric syntax: Expressing a language using a hybrid of language-specific and generic parts
* Exercise 4: Language-parametric transformation: Writing a sanitization transformation that runs on C, Java, JavaScript, Lua, and Python


## To build:

    ./scripts/fastbuild.sh # Normal "stack build" also suffices

## To run your exercises

    stack exec tut1 # Or tut2, tut3, tut4

## To run the standard solutions

    stack exec soln1 # Or soln2, soln3, soln4