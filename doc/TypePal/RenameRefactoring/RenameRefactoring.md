---
title: Rename refactoring
---

#### Synopsis

TypePal offers a framework for rename refactoring. A `Renamer` collects document edits and diagnostics.

#### Description

The rename refactoring is one of the most commonly used refactorings; it renames all corresponding definitions and references to a new name. TypePal includes a framework that enables efficient implementation of rename refactoring for a language by removing boilerplate and generic default behaviour.

::: Prerequisite
The language uses a TypePal-based type-checker.
:::

##### Basic usage

This is an example of a very basic renaming for the `pico` [example](https://github.com/usethesource/typepal/tree/main/src/examples/pico/Rename.rsc).

The first step is to configure the renaming, by at least providing parse and type-check functions.
```rascal
extend analysis::typepal::refactor::Rename;
import examples::pico::Syntax;
import examples::pico::Checker;

RenameConfig picoRenameConfig = rconfig(
    Tree(loc l) { return parse(#start[Program], l); }
  , collectAndSolve
);
```

We can re-use this config for any renaming for `pico`.

::: Caution
To access the functions in the configuration during the various steps of the renaming, use `Renamer::getConfig` to retrieve the config instead of the above declaration. This will ensure the use of internal caches.
:::

Using the configuration, define a rename function.

```rascal
import Exception;

tuple[list[DocumentEdit] edits, set[Message] msgs] renamePico(list[Tree] cursor, str newName) {
    if (!isValidName(newName)) return <[], {error("\'<newName>\' is not a valid name here.", cursor[0].src)}>;
    return rename(cursor, newName, picoRenameConfig);
}

bool isValidName(str name) {
    try {
        parse(#Id, name);
        return true;
    } catch ParseError(_): {
        return false;
    }
}
```

This is enough to get a simple rename refactoring for a language like `pico`. The framework will take care of finding the locations to substitute with the new name automatically. 
The IDE will then apply these text edits.

##### Advanced usage

The framework goes through multiple stages, analysing files and looking for occurrences of the name under the cursor. It takes care of all the bookkeeping. For any stage, there is the possibility of overriding the default behaviour. Overriding works just like for TypePal's type-check functionality, by `extend`ing.

* Resolving the definition(s) of the name under the cursor
* Finding all uses of that declaration
* Checking that no definitions with the new name already exist
* Finding where the name is in the definition tree
* Producing the edits to fulfil the actual renaming

###### Advanced configuration

The `RenameConfig` exposes some additioanl properties through optional keyword arguments. For reference see [here](https://www.rascal-mpl.org/docs/Packages/Typepal/API/analysis/typepal/refactor/Rename/#analysis-typepal-refactor-Rename-RenameConfig).

Additionally, one can extend the configuration with keyword arguments, for example to retain some state for a single rename. Example:

```rascal
extend analysis::typepal::refactor::Rename;
import examples::pico::Syntax;
import examples::pico::Checker;

data RenameConfig(set[loc] workspaceFolders = {});

tuple[list[DocumentEdit] edits, set[Message] msgs] renamePico(list[Tree] cursor, str newName, set[loc] workspaceFolders)
    = rename(cursor
           , newName
           , rconfig(
                Tree(loc l) { return parse(#start[Program], l); }
              , collectAndSolve
              , wokspaceFolders = workspaceFolders
            )
    );
```

###### Resolving definitions

Resolve the name under the cursor to definition(s).

```rascal
set[Define] getCursorDefinitions(Focus cursor, Tree(loc) getTree, TModel(Tree) getModel, Renamer r);
```

The default implementation only looks for definitions in the file where the cursor is. 

###### Find relevant files

Find files in which the following might occur (over-approximation):

* Definitions of the name under the cursor.
* References to/uses of aforementioned definitions.
* Definitions or uses of the new name.

```rascal
tuple[set[loc] defFiles, set[loc] useFiles, set[loc] newNameFiles] findOccurrenceFiles(set[Define] cursorDefs, Focus cursor, str newName, Tree(loc) getTree, Renamer r);
```

The default implementation only looks at the file where the cursor is. For multi-file projects, this step should probably consider more files. If the number of files in projects can be large, it is wise to consider performance when overriding this function.

1. The amount of work done per file should be reasonable.
2. The files returned here will be the inputs to the next steps. Most of those steps will trigger the type-checker on the file first. If type-checking is expensive, try not to over-approximate too liberately here.

###### Find additional definitions

For each files in `defFiles` from [the previous step](#find-relevant-files), find additional definitions to rename.

```rascal
set[Define] findAdditionalDefinitions(set[Define] cursorDefs, Tree tr, TModel tm, Renamer r);
```

The default implementation returns the empty set. The following example overrides the default to find overloaded definitions.

```rascal
extend analysis::typepal::refactor::Rename;

set[Define] findAdditionalDefinitions(set[Define] defs, Tree _, TModel tm, Renamer _) =
    {
      tm.definitions[d]
    | loc d <- (tm.defines<idRole, id, defined>)[defs.idRole, defs.id] - defs.defined
    , tm.config.mayOverload(defs.defined + d, tm.definitions)
    };
```

###### Validate occurrences of new name

For all `newFiles` from the [selected files](#find-relevant-files), check if renaming `cursorDefs` will cause problems with the existing occurrences of `newName` in the file.

```rascal
void validateNewNameOccurrences(set[Define] cursorDefs, str newName, Tree tr, Renamer r);
```

The default implementation raises an error when a occurrence of `newName` exists here.

###### Find name location

Finds the location of the name in a definitions parse tree.

```rascal
loc nameLocation(Tree t, Define d);
```

The default implementation returns the location of the first sub-tree of which the un-parsed representation matches the name of the definition. If no match is found, it returns the location of the parse tree.

###### Rename definition

Rename a single definition, with its name at `nameLoc` (determined by [the previous function](#find-name-location)) to `newName`. This is called for each definition collected by `getCursorDefinitions` and `findAdditionalDefinitions`.

```rascal
void renameDefinition(Define d, loc nameLoc, str newName, TModel tm, Renamer r);
```

The default implementation registers an edit to replace the text at `nameLoc` with `newName`. Overriding this can be useful, e.g. if extra checks are required to confirm the rename is valid, or if the renaming requires additional edits, like moving a file.

###### Rename uses

In a single file, rename all uses of the definitions. This is called for all `useFiles` from the [selected files](#find-relevant-files).

```rascal
void renameUses(set[Define] defs, str newName, TModel tm, Renamer r);
```

The default implementation registers edits to replace the text at any use with `newName`. Overriding this can be useful, e.g. if extra checks are required to confirm the rename is valid, or if additional edits are necessary.
