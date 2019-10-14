# TypePal

An experiment in type checker generation. _Warning: work in progress!_

From the user perspective the basic idea is as follows:

1. Start with a Rascal grammar of the language of interest, say, MiniML.
2. Write functions for specific language constructs
   - `define` captures all defining occurrences of variables and their scopes;
   - `use` captures all uses of variables;
   - `require` captures all static requirements on the use of certain constructs, such formal/actual parameter correspondence and the like;
    - `calculate` to compute a type for a language fragment using earlier calculated types, think of the result type of an operator based on its argument types.
3. The above functions will populate a fact/requirement model (or `TModel` for short) of a source program to be type checked.
4. Apply the `collect` function to a parsed program (a parse tree). This will apply `define`/`use`/`require`/`calculate` to all relevant places in the tree, will create scopes and use/def information and will also build a collection of constraints. They are all part of the `TModel`.
5. Apply `solve` to the `TModel` resulting from the previous step. `solve` is happy if all constraints can be solved and generates error messages otherwise. `solve` also enhances the original `TModel` with derived facts that can be used for use/def analysis, interactive display of type information, and the like.
