# TypePal

An experiment in type checker generation. _Warning: work in progress!_

From the user perspective the basic idea is as follows:

1. Start with a Rascal grammar of the language of interest, say, MiniML.
2. Write functions for specific language constructs
   - `define` captures all defining occurrences of variables and their scopes
   - `use` captures all uses of variables
   - `require` captures all static requirements on the use of certain constructs, think of argument types of operators,      formal/actual parameter correspondence and the like.
3. Apply the `extractScopesAndConstraints` function to a parsed program (a parse tree). This will apply `define`/`use`/`require` to all relevant places in the tree, will create scopes and use/def information and will also build a collection of constraints.
4. Apply `validate` to the result of the previous step. `validate` is happy if all constraints can be solved and generates error messages otherwise.
