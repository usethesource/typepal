---
title: TypePal Configuration
---
  
#### Synopsis

Configuration options for TypePal

## Description

TypePal provides configuration options for

* _Name Resolution & Overloading_: configures how names are resolved and which overloading is allowed.
* _Operations on Types_: configures how operations like subtype and least-upper-bound (lub) are defined.
* _Retrieval of Types_: configures how named and structured types are handled.
* _Extension Points_: configures operations before an after solving.
* _Miscellaneous_: utility functions that can be configured.

Here is an overview:

![]((TypePalConfig.png))

### Name Resolution & Overloading

####  isAcceptableSimple
```rascal
/* Configuration field */ Accept (TModel tm, loc def, Use use) isAcceptableSimple
```

Here

* `tm` is a given TModel
* `def` is a proposed definition
* `use` is the use 
  (characterized by the `Use` data type that contains, name, occurrence, scope and identifier roles of the use
  for which the definition is proposed.

`isAcceptableSimple` accepts or rejects a proposed definition for the use of a simple name in a particular role. 
The returned `Accept` data type is defined as:
```rascal
data Accept 
    = acceptBinding()
    | ignoreContinue()
    | ignoreSkipPath()
    ;
```

The default `isAcceptableSimple` returns acceptBinding()`.

Typical concerns addressed by `isAcceptableSimple` are:

* enforce definition before use;
* check access rights, e.g. visibility.

By comparing the offset of the source locations of definition, respectively, the use,
we enforce definition before use:

```rascal
Accept myIsAcceptableSimple(TModel tm, loc def, Use use)
    = use.occ.offset > def.offset ? acceptBinding() : ignoreContinue();
```

#### isAcceptableQualified
```rascal
/* Configuration field */ Accept (TModel tm, loc def, Use use) isAcceptableQualified
```
Here

* `tm` is a given TModel
* `def` is a proposed definition
* `use` is the use for which the definition is proposed.

`isAcceptableQualified` accepts or rejects a proposed definition for the use of a qualified name in a particular role.
  
#### isAcceptablePath
```rascal
/* Configuration field */ 
Accept (TModel tm, loc defScope, loc def, Use use, PathRole pathRole) isAcceptablePath
```
Here

* `tm` is a given TModel;
* `defScope` is the scope in which the proposed definition occurs;
* `def` is a proposed definition;
* `use` is the use for which the definition is proposed;
* `pathRole` is the role of the semantic path.

`isAcceptablePath` accepts or rejects a proposed access path between use and definition.

To illustrate this, assume a language with modules and imports. A module may contain variable definitions
but these are not visible from outside the module. This can be enforced as follows:

```rascal
Accept myIsAcceptablePath(TModel tm, loc def, Use use, PathRole pathRole) {
    return variableId() in use.idRoles ? ignoreContinue() : acceptBinding();
}
```

#### mayOverload
```rascal
/* Configuration field */ bool (set[loc] defs, map[loc, Define] defines) mayOverload 
```

`mayOverload` determines whether a set of definitions (`defs`) are allowed to be overloaded,
given their definitions (`defines`).

For example, [Featherweight Java]((examples::fwjava::Checker)) the only allowed overloading is between class names and constructor names.
```rascal
bool fwjMayOverload (set[loc] defs, map[loc, Define] defines) {
    roles = {defines[def].idRole | def <- defs};  //<1>
    return roles ### {classId(), constructorId()}; //<2>
}
```
<1> First collect all the roles in which the overloaded names have been defined.
<2> Only allow the combination of class name and constructor name.


### Operations on Types
Various operations on types can be configured by way of user-defined functions.

#### isSubType
```rascal
/* Configuration field */ bool (AType l, AType r) isSubType 
```
Function that checks whether `l` is a subtype of `r`.

#### getLub
```rascal
/* Configuration field */ AType (AType l, AType r) getLub
```
Function that computes the least upperbound of two types and `l` and `r`.

#### getMinAType
```rascal
/* Configuration field */ AType() getMinAType 
```
Function that returns the _smallest_ type of the type lattice.

#### getMaxAType
```rascal
/* Configuration field */ AType() getMaxAType
```
Function that returns the _largest_ type of the type lattice.

#### instantiateTypeParameters
```rascal
/* Configuration field */ AType (Tree current, AType def, AType ins, AType act, Solver s) instantiateTypeParameters
```

The function `instantiateTypeParameters` defines instantiation of *language-specific* type parameters, where:

* `current` is a source code fragment for which type `act` has already been determined, but any *language-specific* type parameters
  in `act` may still need to be instantiated.
* `def` is the parameterized type of `act`.
* `ins` is an instantiated version of the type of `act` (i.e., with bound type parameters).
* `act` is the actual type found for `current` that needs to be instantiated.

`instantiateTypeParameters` will match `def` with `ins` and the resulting bindings will be used to instantiate `act`.
The instantiated version of `act` is returned.

In the [StructParameters demo]((examples::structParameters::Checker)) parameterized structs (records) are defined. 
The formal type of such a struct is ``structDef(str name, list[str] formals)``, 
i.e., a struct has a name and a list of named formal type parameters.
The actual type of a struct is ``structType(str name, list[AType] actuals)``, 
i.e., a struct name followed by actual types for the parameters.

The definition of `instantiateTypeParameters` for this example is as follows:

```rascal
AType structParametersInstantiateTypeParameters(Tree current, structDef(str name1, list[str] formals), structType(str name2, list[AType] actuals), AType t, Solver s){
    if(size(formals) != size(actuals)) throw checkFailed([]);
    bindings = (formals[i] : actuals [i] | int i <- index(formals));
    
    return visit(t) { case typeFormal(str x) => bindings[x] };
}

default AType structParametersInstantiateTypeParameters(Tree current, AType def, AType ins, AType act, Solver s) = act;
```

### Retrieval of Types

#### getTypeNamesAndRole
```rascal
/* Configuration field */  tuple[list[str] typeNames, set[IdRole] idRoles] (AType atype) getTypeNamesAndRole
```
This function determines whether a given `atype` is a named type or not. This is needed for the customization
of indirect type computations such as `useViaType` and `getTypeInType`. When `atype` is a named type
`getTypeNamesAndRole` returns:

* A list of names that may be associated with it. In most languages this will contain just a single element, the name of the type.
  In more sophisticated cases the list may contain a list of named types to be considered.
* A list of roles in which the type name can be bound.

Here are the definitions for the [Struct demo]((examples::struct::Checker)):
```rascal
tuple[list[str] typeNames, set[IdRole] idRoles] structGetTypeNamesAndRole(structType(str name)){
    return <[name], {structId()}>; //<1>
}

default tuple[list[str] typeNames, set[IdRole] idRoles] structGetTypeNamesAndRole(AType t){
    return <[], {}>;               //<2>
}
```
<1> A `structType(name)` has a name that is bound in the role `structId()`. Return the name and role.
<2> Any other type is unnamed; return an empty list of type names.

Another example is the Rascal type checker, where we need to model the case that all abstract data types are a subtype of `Tree`.
In that case `getTypeNamesAndRole` will return `<["A", "Tree"], roles>` for an abstract data type `A`. The net effect
is that when the search for a name in `A` fails, the search is continued in `Tree`.

#### getTypeInTypeFromDefine
```rascal
/* Configuration field */  AType (Define containerDef, str selectorName, set[IdRole] idRolesSel, Solver s) getTypeInTypeFromDefine
```
In some extreme cases (think Rascal) the type of a field selection cannot be determined by considering all the fields
defined in a container type and as a last resort one needs to fall back to information that has been associated with the original definition
of the container type. `getTypeInTypeFromDefine` is called as a last resort from `getTypeInType`.

In the Rascal type checker common keyword parameters of data declarations are handled using `getTypeInTypeFromDefine`.


#### getTypeInNamelessType
```rascal
/* Configuration field */ AType(AType containerType, Tree selector, loc scope, Solver s) getTypeInNamelessType
```
`getTypeInNamelessType` describes field selection on built-types that have not been explicitly declared with a name.
A case in point is a `length` field on a built-in string type.

In [the StaticFields demo]((examples::staticFields::Checker)))) this is done as follows:
```rascal
AType staticFieldsGetTypeInNamelessType(AType containerType, Tree selector, loc scope, Solver s){
    if(containerType ### strType() && "<selector>" ### "length") return intType();
    s.report(error(selector, "Undefined field %q on %t", selector, containerType));
}
```

### Extension Points
    
#### preSolver
```rascal
/* Configuration field */ TModel(map[str,Tree] namedTrees, TModel tm) preSolver
```
A function `preSolver` that can enrich or transform the TModel before the Solver is applied to it.

#### postSolver
```rascal
/* Configuration field */ void (map[str,Tree] namedTrees, Solver s) postSolver
```
A function `postSolver` that can enrich or transform the TModel after constraint solving is complete.


### Miscellaneous

#### normalizeName
```rascal
/* Configuration field */  str(str) normalizeName  
```
A function `normalizeName` to define language-specific escape rules for names. By default, all backslashes are removed from names.

#### validateConstraints
```rascal
/* Configuration field */ bool validateConstraints = true
```
When `validateConstraints` is true, the validity of all constraints is checked before solving starts.
For all dependencies (in facts, calculators and requirements) a calculator needs to be present to solve that dependency.

#### createLogicalLoc
```rascal
/* Configuration field */ loc (Define def, str modelName, PathConfig pcfg) createLogicalLoc
```
Internally, TypePal operates on physical source locations, e.g., source locations that point to a specific location in a source file. This all works fine, until modules and separate compilation come into play. Case in point is a function `f` declared in file A that is used in file B. When file A is edited, the source location of `f` will most likely change, while in most cases the definition of `f` has not been changed. Any information based on `f`'s original source location will be broken. To solve this problem _logical source locations_ are introduced that abstract away from the precise source locations and are thus better.

Given a Define `def`, the function `createLogicalLoc` returns the logical version of `def.defined` if desired, otherwise it returns `def.defined` unmodified. This function gives complete freedom for which `IdRole`s logical locations will be generated and in what way they are encoded. In the case of a simple functional language called `fun`, the function `f` will, for instance, be encoded as `|fun+function:///A/f|`. In the case of Rascal where extensive function overloading is present, we generate `|rascal+function:///A/f$abcde|`, where `$abcde` is a prefix of the md5hash of the complete function declaration of `f`.


:::warning
When a function is overloaded, measures have to be taken to create unique logical locations for each overloaded variant of that function. A naive solution is to use the line number of the declaration. A more solid solution is to use a hash of the actual contents of the function to distingush each function variant.
:::