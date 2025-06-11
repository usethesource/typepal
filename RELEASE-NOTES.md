##  Release 0.11.5 

* Administrative release that prepares for a complete Rascal bootstrap
* RELEASE-NOTES added for the benefit of the generated documentation

##  Release 0.11.4 

* Minor changes for version checking

##  Release 0.11.3 

* Fixed error in intercalateAnd and intercalateOr.

##  Release 0.11.2 

* Fixed subtle omission in isAlreadyDefined

##  Release 0.11.1 

* Improved error messages

##  Release 0.11.0 

* Fixed test that expected error message that is no longer generated
* Removed redundant print: "Skipping (type-incorrect) def"
* Clean up
* Fixed error reduction
* Reduce number of generated error messages
    
    "Reference to name ..." and "Reference to type ..." messages are
    suppressed if there is already an error for the same location

##  Release 0.10.0 

* Fixed incorrect default for `defaultLogicalLoc`
* Code clean up
* Removed outdated configuration options.
* Changes related to different handling of logical locations
* Added a high-level comment to each module
* Added missing configuration option
* Updated documentation
* Fixed erroneously commented out line
* First version of logical locs; all tests succeed
   * logical locs give qualified names to all externally visible declared roles
   * this way a module may change internally, but if the external logical locs
     do not change, then the module is binary backward compatible from the perspective
     of typepal type checking and name resolution.

##  Release 0.9.0 

* Added some type declarations

##  Release 0.8.6 

* added zenodo software citation
* Described funding and citation for typepal
* Added example to answer question on stackoverflow
    
    See https://stackoverflow.com/questions/76502168/writing-semantic-rules-with-typepal

* Minor changes related to Rascal compiler development
* Added example: a struct declaration split over several declarations

##  Release 0.8.5 

* improved error message for missing collect for large trees (shortened and added ...)
* fixed missing case for parametrized-lex and changes warnings to info for missing collect cases
* Turn all hard failures for missing collect or calculator into warnings
    
    This is an experiment to enable writing partial type checkers, e.g. to
    only calculate use-defs.

* Make sure to make new variables
    
 Normally this isn't an issue, but since `TestFramework` needs to be extended in the module it's used, an import of `DateTime` can break this code, as `parseTime` is a function.

##  Release 0.8.3 

* added source and issues for generating main tutor page

##  Release 0.8.2 

* Better use of the newest rascal-tutor features

##  Release 0.8.1 

* Documentation was improvied
   * experiment to fix weird links
   * fixed some header syntax
   * fixed links and anchors and headings

##  Release 0.8.0 

* Updated dependencies such that newer downstream dependencies can use typepal
* resolved all broken links for the tutor in the markdown files
* more links fixed
* fixed link errors in Configuration.md
* Made some loc handling more robust

##  Release 0.8.0 

* Updated dependencies such that newer downstream dependencies can use typepal
* Experimenting with new tutor compiler

##  Release 0.7.9 

* First iteration of optimizing getId/use
* included TypePal documentation in typepal project, for later processing by the tutor compiler when it is released
* Fixed glitch in path name (thx @DavyLandman)
* Added evenOdd example
* Rewritten definitions of predefined class and constructor "Object"
* Changes to ICollector API
* Slightly modified/extended the ICollector API
   - removed getPredefinedTree
   - added predefineInScope
   - predefine and predefineInScope now return the (synthetic) Tree of the
     new definition
* Fixed intialization bug introduced when rewriting code to suit compiler
* Avoided a syntax rule just to get a loc
* added a BSD-2 license file to start fixing #4
* Avoided a syntax rule just to get a loc
* Changes to enable compilation of TypePal

##  Release 0.7.4-0.7.8 

* Made tests robust against different execution orders of solver
* In TTL tests: expect {m1, m2, ...} now means expect ONEOF m1, m2, ...
* Fixed side effect of changed definition of Define.

##  Release 0.7.3 

* Improved version handling

* Commented out picoci tests to avoid Rascal evaluator bug

##  Release 0.7.2 

* Added basic machinery for versioning TPL files
* Fixed some type warnings
* Fix related to Issue #1588

##  Release 0.7.0-0.7.1 

* Added support for case-independent names
* Added case-independent Pico
* Added to collector: predefine and getPredefinedTree
* Added missing check and simplications (thx @rodinaarsen)
* Added missing case for brackets (thx @rodinaarsen)

##  Release 0.6.2 

* Solved another quoting issue in formatted messages
* Fixed issue with quoting in formatted messages.

##  Release 0.6.1 

* Fixed issue in message formatting print order
* Changed back src => loc
* Fixed yaml
* Fixed typepal crashing the maven compiler

##  Release 0.6.0 

* Removed some loc annotations
* Some error recovery in case of type errors

##  Release 0.5.0-0.5.4 

* Upgrading package to Java 11

##  Release 0.4.12 

* Minor restructuring to fix error so correctly found by typechecker
* Eliminate all defTypeCalls before handing control to the postSolver

##  Release 0.4.11 

* Cleaning up typepal and the size of the generated jar
* Trying to run compiler in parallel
* Added missing match that caused parsetrees to be included in TModel
* Print extra debug info
* Further simplifcations to faciltate down stream usage
* Renaming + further simplification

##  Release 0.4.9 

* Merged with restructure branch and clean up
* Major simplification/restructuring that removes all import and extend cycles

##  Release 0.4.8 

* removed left-overs from when this was an Eclipse project
* removed all unused Eclipse metadata to prevent Eclipse from picking it up and producing ambiguous classpaths for projects depending on typepal
* removed package stage because that is already triggered (and again) by install
* Added tests for the string case
* Added missing rule for string literal in syntax
* removed dead StrCon case and fixed expected replies of type-checker
* changed packaging of typepal to a normal jar (as opposed to an Eclipse bundle)

##  Release 0.4.6-0.4.7 

* Made global store functionality in Solver identitical to Collector
* Fixed error in recent change
* Polished double declaration reporting
* Added declaration links to double declaration error message
* Made getLoc more robust against literals at front of the production
* Disabled println if not in verbose mode
* Improvements & optimizations to the inference engine

##  Release 0.4.4 

* Eliminated use of isContainedIn for scope inclusion
* Added link to repository to find the pom parent

##  Release 0.4.3 

* Removed two defensive throws, that are actually legal cases
* Removed more warnings
* Temporarily turned off packaging for typepal to avoid readBinaryFile bug

##  Release 0.4.2 

* Changing the version to reflect the pom versions for the release
* Added more precise typing to `defType` 

##  Release 0.4.1 

* Added `getType` on Collectors
* Added missing returns;
* Fixed various missing returns

##  Release 0.4.0 

* Reorganization: fully typechecked, better modularization, same API
* Added testsuite to run at command line
* Removed a number of type errors

##  Release 0.3.0 

* Fixed error due to recent change in ScopeGraph
* Disabled FWJTests for now
* Some (unfortunately breaking) API changes
    
    In the following three functions the TModel parameter is replaced by a
    Solver andthe parameter has been moved to the end for consistency
    reasons.
    
       Accept isAcceptableSimple(TModel tm, loc def, Use use)
    => Accept isAcceptableSimple(loc def, Use use, Solver s)
    
       Accept isAcceptableQualified(TModel tm, loc def, Use use)
    => Accept isAcceptableQualified(loc def, Use use, Solver s)
    
       Accept isAcceptablePath(TModel tm, loc defScope, loc def, Use use,
    PathRole pathRole)
    => Accept isAcceptablePath(loc defScope, loc def, Use use, PathRole
    pathRole, Solver s)
    
    Solver:
      Renamed:
        getAllDefinitions => getAllDefines
      New:
        Paths getPaths()
        Define define(loc def)

* added more memory to typepal

##  Release 0.2.1 

* added config
* included release config here because it can not be inherited from the parent
* turned off errorsAsWarnings since we do not have errors anymore
* temporary copy of lang/std modules for use in the examples, until the standard library lang folder is deployed
* Renamed "union" on locations to "cover"
* removed superfluous clean before package
* added more test files
* renamed build stages
* include ttl files
* commented-in the type-checking of the type-checker
* Restructured to eliminate module variables
* First version with full JUNit test support
* Got the test to run inside maven
* Improved intercalateOr
* Switched default lookup to simple lookup (opposed to lookupWide)
* Removed undesired use-defs (while checking unused defines)
* Added check on double declaration of unused variables
* Added progress message
* Added simple utility function to extract tests defined in a TTL file
* Fixed dead code/missing return errors
* Fixed error caused by moving code from Rascal checker to TypePal
* Fix for amb tree without offset
* Improved organization and performance
* Code cleanup (driven by automatic unused name detection)
* Further support for unused names + cleanup
* Added configurable reporting for unused names.
* Removed (unused) argument from TypeUnavailable constructor
* Moved prettyRole
* Added specializedFacts and misc code improvements
* Added isInferrable as config option
* Added Ascii spinner on special request of @DavyLandman
* Added runName parameter to runTests
* Simplified (and corrected) unify
* Added forgotten simplication case for lazyLub
* Renamed prettyPrintAType => prettyAType
* Further stabilizing TypePal
    
    TypePalConfig:
    Old:
    tuple[bool isNamedType, str typeName,
          set[IdRole] idRoles] (AType atype) getTypeNameAndRole
    New:
    tuple[list[str] typeNames, set[IdRole] idRoles] (AType atype)
    getTypeNamesAndRole
    
    Note: Now returns a list of possible type names (enables forms of
    inheritance). isNamedType <==> !isEmpty(typeNames)
    
    New:            bool verbose                = false,
    New:    bool showTimes              = false,
    New:    bool showSolverSteps        = false,
    New:    bool showSolverIterations   = false,
    New:    bool showAttempts           = false,
    New:    bool showTModel             = false,
    New:    bool validateConstraints    = true,
    Note:   Detailed flags to control output verbosity
    
    Solver:
    
    New:            void (list[Message]) addMessages
    Note:   Add (ordinary) messages generated by other components
    
    New:            bool () reportedErrors
    Note:   True when at least one error has been reported.

* Gradually evolving the framework. Added support for components
* Added getTypeInScopeFromName
* More precise usedefs
* First shot at maintaining usedef relation for indirect uses
* Only report secondary errors when no primary errors are found
* Make sure the getAllDefinedInType throws in case the information has not been resolved yet
* Replaced (and extended) getAllTypesInType by getAllDefinedInType
* Speed/functionality improvements to collect
* Added small test framework feature to pass in a list of test functions to run
* Made interpolate robust against TypeUnavailable()
* Faster collect, various improvements
* The body of the tests can now handle nested angle brackets better
* Everything that extends, now also keeps extending
* Major reorganization and optimization
* Added require[Equal,Comparable,Subtype] to Collector
* Ignore empty reports
* Added getAllTypesInType, requireTrue, requireFalse to Solver
* Removed ambigity from the multi-line comment
* replaced FailMessage constructors with varargs functions
* A new solution for field selection, distinguishing names types from unnamed types.
    
    We distinguish named types (typically records and ADTs) and
    unnamed types (e.g., other types like strings, lists of ints)
    
    Defining a field selection on any type is done by `useViaType`.
    This is supported by some user-supplied functions that can be defined
    via the TypePal configuration:
    
            getTypeNameAndRole:
                    determine if a types is a named type
            getTypeInNamelessType:
                    handle field selection for unnamed types
    
    Some more details.
    
    For collector:
             void (Tree container, Tree selector,
                   set[IdRole] idRolesSel) useViaType
    
    During solving useViaType will call the following user-supplied
    functions:
    
            tuple[bool isNamedType, str typeName, set[IdRole] idRoles]
            (AType atype) getTypeNameAndRole
    
            If `atype` is a named type, return its name and the role via
            which it can be bound.
    
    and
    
            AType(AType containerType, Tree selector,
                  set[IdRole] idRolesSel, loc scope, Solver s)
                  getTypeInNamelessType
    
            In an unnamed containerType, return the type of selector in
            one of the roles isRolesSel.
            (For a named type this is handled automatically)

* Removed %s, as %v already did that
* Handle other values differently from normal strings
* Added %s  to the fmt function
* Refactored
   * Solver moved to separate module.
   * Only a single extend is now enough:
            `extend analysis::typepal::TypePal;`

* Renamed ExtractTModel => Collector
* Moved Message handling to separate module
* Working on preATypes
* list/set issue with messages
* Alternative approach: removing timestamps inside .tpl file
* Internally switch from set[Message] to list[Message]
* Another time stamp overloading case
* Factored out findMostRecentDef
* Take time stamps into account wrt overloading
* Removed @memo on getType (for debugging)
* Removed last declaration of deescape
* Extended TTL_StringCharacter
* Fixed some glitches in new configuration style
* New: TypePalConfig; Various improvements
   * All functions (except collect) now defined in TypePalConfig
   * resolvePaths is now called automatically.
   * Dependencies are lists (again), gives better error messages
   * In case a require or calculate cannot be satisfied: only give
     a generic error message when there are now messages for parts
     of the subject of require/calculate
   * Simplified code in various places
* Reshuffling/renaming; new: alreadyReported for message filtering
* Added getDefinitions(Tree tree, set[IdRole] idRoles) function
* Report better error in case of amb parse
* Added defineInScope to simplify function checking
* Added loop prevention for triggers
* Report accurate parsing errors
* Improved handling of defLubs; many small changes
* Removed another source of non-determinism
* Put back old relocate; fixed a remaining set[Message]
* Fixed loc calculation when there are no line numbers
* TypePal can now be compiled
* Improved encoding of typevars
* Accuratly calculate the result of the test framework call
* Made single line comment a bit less amb
* Fixed order of error messages
* Added back the newer interface for test framework, and sorted all messages
* Import TypePal snapshot from rascal-core
* Changed test framework to relocated the locations from the start
* Moving old typepal code to the new location
* Major progress with experimental Rascal type checker
   * completely reorganized in separate modules
   * implemented import/extend
   * implemented data declarations with common keyword parameters
   * instead of reusing Symbol, the ATypes for the Rascal checker are
     becoming self-contained.
   * added many tests
* Reorganization & extension of TypePal to enable Rascal type checking
    
    Removed:
            - The concepts of usedType (an indirect reference to a defined type)
              since it is not expressive enough to handle Rascal ADTs and common
              keyword fields. Replaced by a version of `typeof` that enables
              lookup of a name (e.g. an ADT name) in a given scope.
    Added:
            - "lookupWide", a version of lookup that is better compatible with
              the Rascal scope model. This is now a parameter of extract and
              validate.
    
    Renamings:
            AType2String -> prettyPrintAType
            overloadedType -> overloadedAType

* Minor changes/addition in preparation for next step in Rascal checking
* Refactored Rascal checker in separate modules
* qualified type is necessary for correct continous release
* Factored out Rascal specific ATypes; updated reporting style
* Undone "fancier" reporting in favour of uniformity
* Added a "store" to the FRModel
* Refined lub definition
* Improved error reporting; renamings
* Added license header to all rascal files
* Added more error checking; added comments
* added plugin.xml for library release purposes
* Added support for warning and info messages.
* replaced debug while for working solve
* improved undefined diagnostics
* Added mayBeOverloaded to TestFramework
* Fixed edge case error
* different error message for unresolved type or unresolved type dependencies
* split error messages for unresolved identifiers into either completely undefined or undefined due to missing dependencies
* Added a generic "overloadedType" concept
* Various improvements and tests
* Added &&, ||, if-then, if-then-else; scoping fun :-)
* Messages are now part of the FRModel; added "comparable" predicate
* Added debug parameter; debugging can now be turned on from the outside
* Started with TypePal documentation
* Some initial Rascal typechecking experiments
* PCI language: packages/class/interfaces exploring kastens/waite examples
* Further evolving the TypePal framework
* Reorganized directories
* Improved output of runTests; added verbose option
* Improved comments in TTL and added register function
* Deescape expected strings
* Relaxed getUseDef
* Added functions to extracts data from model
* changed signature of validate: noew return messages and model
* Rather stable version of direct execution version, move it to main
* Progress with refactoring to direct execution
* Half way converting to direct execution style
* (Not yet complete) type checker for Pascal
* Started with FeatherweightJava
* Major extension/rewrite of examples
* Major rewrite of unification and instantiation
* first commit
