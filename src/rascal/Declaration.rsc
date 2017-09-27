module rascal::Declaration

extend typepal::TypePal;

import lang::rascal::\syntax::Rascal;
import rascal::ConvertType;
//import lang::rascal::types::AbstractName;
import rascal::ATypeUtils;
import rascal::ATypeInstantiation;

extend rascal::AType;
extend rascal::Scope;

// ---- Rascal declarations

Tree define(m: (Module) `<Header header> <Body body>`, Tree scope, FRBuilder frb){
    frb.define(scope, "<header.name>", moduleId(), m, defType(amodule("<header.name>")));
    return m;
}

void collect(imp: (Import) `import <ImportedModule m> ;`, Tree scope, FRBuilder frb){
    frb.use_ref(scope, m.name, {moduleId()}, importPath());
}

void collect(imp: (Import) `extend <ImportedModule m> ;`, Tree scope, FRBuilder frb){
    frb.use_ref(scope, m.name, {moduleId()}, extendPath());
}

Vis getVis((Visibility) `private`)  = privateVis();
Vis getVis((Visibility) `public`)   = publicVis();
Vis getVis((Visibility) ``)         = defaultVis();

// Note: Rascal's closures are mutable, therefore we need an extra closure when creating
// several requirements from the same function context. In this way the value of expr becomes fixed
void() makeVarInitRequirement(Expression expr, AType initType)
    = () { 
           subtype(typeof(expr), initType, onError(expr, "Type of initialization should be subtype of <fmt(initType)>, found <fmt(expr)>"));
         };
         
Tree define(varDecls: (Declaration) `<Tags tags> <Visibility visibility> <Type \type> <{Variable ","}+ variables> ;`, Tree scope, FRBuilder frb){
    vis = getVis(varDecls.visibility);
    if(vis == defaultVis()){
        vis = privateVis();
    }
    varType = convertType(varDecls.\type, frb);
    
    for(var <- variables){
        frb.define(scope, "<var.name>", variableId(), var.name, defType(varType, vis=vis));
        if(var is initialized){
            frb.require("variable initialization", var.initial, [], makeVarInitRequirement(var.initial, varType));
        }
    }
    return scope;
} 

list[Expression] getReturnExpressions(Tree decl)
    = [expr | /(Statement) `return <Expression expr>;` := decl];

// Note: Rascal's closures are mutable, therefore we need an extra closure when creating
// several requirements from the same function context. In this way the value of expr becomes fixed
void() makeReturnRequirement(Expression expr, AType retType, list[Pattern] formals, set[str] kwTypeVars)
       = () { typeVarsInParams = {*collectTypeVars(typeof(f)) | f <- formals} + kwTypeVars;
              typeVarsInReturn = collectTypeVars(retType);
              if(!(typeVarsInReturn <= typeVarsInParams)){
                reportError(signature.\type, "Unbound type variable in return type");
              }
              //println("makeReturnRequirement, <expr>, <typeof(expr) ? "undefined">");
             if(isFullyInstantiated(typeof(expr))){
                subtype(typeof(expr), retType, onError(expr, "Return type should be subtype of <fmt(retType)>, found <fmt(expr)>"));
              } else {
              if(!unify(typeof(expr), retType)){
                 subtype(typeof(expr), retType, onError(expr, "Return type should be subtype of <fmt(retType)>, found <fmt(expr)>"));
              }
           }
         };
             
Tree define(FunctionDeclaration decl, Tree scope, FRBuilder frb){
    visibility = getVis(decl.visibility);
    if(visibility == defaultVis()){
        visibility = publicVis();
    }
    signature = decl.signature;
    
    params = signature.parameters;
    formals = [pat | Pattern pat <- params.formals.formals];
    
    // Take care of single variable patterns
    defineSingleVarsInFormals(formals, decl, frb);
  
    fname = signature.name;
    retType = convertType(signature.\type, frb);
    kwFormals = [];
    
    if(params.keywordFormals is \default){
        kwFormals = getKeywordFormals(params.keywordFormals.keywordFormalList, decl, frb);
    }
    
    dt = defType(formals, AType() { return afunc(retType, atypeList([typeof(f) | f <- formals]), kwFormals); });
    dt.vis=visibility;  // TODO: Cannot be set directly, bug in interpreter?
    frb.define(scope, "<fname>", functionId(), fname, dt);
    
    kwTypeVars = {*collectTypeVars(kwf.fieldType) | kwf <- kwFormals};
    frb.require("bound type variables", decl, formals,
        () { typeVarsInParams = {*collectTypeVars(typeof(f)) | f <- formals} + kwTypeVars;
             typeVarsInReturn = collectTypeVars(retType);
             if(!(typeVarsInReturn <= typeVarsInParams)){
                reportError(signature.\type, "Unbound type variable in return type");
             }
        });
    if(decl is \default){
        for(Expression expr <- getReturnExpressions(decl)){
            frb.requireEager("return type", expr, [expr], makeReturnRequirement(expr, retType, formals, kwTypeVars));     
        }
    } else
    if(decl is expression){
        frb.requireEager("return type", decl.expression, [decl.expression], makeReturnRequirement(decl.expression, retType, formals, kwTypeVars));
    } else
    if(decl is conditional){
        frb.requireEager("return type", decl.expression, [decl.expression], makeReturnRequirement(decl.expression, retType, formals, kwTypeVars));
        conditions = [c | c <- decl.conditions];
        frb.requireEager("when conditions", decl.conditions, conditions,
            (){
            for(cond <- conditions){
                if(isFullyInstantiated(typeof(cond))){
                    subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                } else {
                    if(!unify(typeof(cond), abool())){
                        subtype(typeof(cond), abool(), onError(cond, "Condition should be `bool`, found <fmt(cond)>"));
                    }
                }
            }
        });
    }
    return decl;
}

void defineSingleVarsInFormals(list[Pattern] pats, Tree scope, FRBuilder frb){
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            frb.atomicFact(pat, avalue());
            frb.define(scope, "<name>", formalId(), name, defLub([], AType() { return avalue(); }));
        }
        if(splicePat: (Pattern) `*<QualifiedName name>` := pat || splicePat: (Pattern) `<QualifiedName name>*` := pat){            
            frb.atomicFact(pat, avalue());
            frb.define(scope, "<name>", formalId(), name, defLub([], AType() { return alist(avalue()); }));
        }
        if(splicePlusPat: (Pattern) `+<QualifiedName name>` := pat){
            frb.atomicFact(pat, avalue());
            frb.define(scope, "<name>", formalId(), name, defLub([], AType() { return alist(avalue()); }));
        }
    }
}

list[Keyword] getKeywordFormals({KeywordFormal  "," }+ keywordFormalList, Tree scope, FRBuilder frb){    
    return 
        for(KeywordFormal kwf <- keywordFormalList){
            fieldType = convertType(kwf.\type, frb);
            fieldName = "<kwf.name>";
            defaultExp = kwf.expression;
            frb.define(scope, fieldName, formalId(), kwf.name, defType(fieldType));
            append <fieldType, fieldName, defaultExp>;
        }
}
Tree define (decl: (Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters>;`, Tree scope, FRBuilder frb)
    = dataDeclaration(decl, [], scope, frb);

Tree define (decl: (Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters> = <{Variant "|"}+ variants> ;`, Tree scope, FRBuilder frb)
    = dataDeclaration(decl, [v | v <- variants], scope, frb);

Tree dataDeclaration(Declaration decl, list[Variant] variants, Tree scope, FRBuilder frb){
    userType = decl.user;
    commonKeywordParameters = decl.commonKeywordParameters;
    adtName = "<userType.name>";
   
    dataTypeVars0 = [];
    if(userType is parametric){
       dataTypeVars0 =
            for(p <- userType.parameters){
                ptype = convertType(p, frb);
                if(!isTypeVar(ptype)){
                  frb.reportError(p, "Only type parameter allowed, found <fmt(ptype)>");
                }
                append ptype;
            }
    }
    dataTypeVars = toSet(dataTypeVars0);
    
    commonKwFields = [];
    if(commonKeywordParameters is present){
        commonKwFields = getKeywordFormals(commonKeywordParameters.keywordFormalList, decl, frb);
    }
    adtType = aadt(adtName, dataTypeVars0, commonKwFields);
    frb.define(scope, adtName, dataId(), userType.name, defType(adtType));
    
    for(Variant v <- variants){
        consName = "<v.name>";
        allFieldTypeVars = {};
        fields = 
            for(TypeArg ta <- v.arguments){
                fieldType = convertType(ta.\type, frb);
                fieldName = ta has name ? "<ta.name>" : "";
                allFieldTypeVars += collectTypeVars(fieldType);
                append <fieldType, fieldName>;
            }
    
       kwFields = [];
       if(v.keywordArguments is \default){
          kwFields += getKeywordFormals(v.keywordArguments.keywordFormalList, decl, frb);
          for(<kwt, kwn,kwd> <- kwFields){
              allFieldTypeVars += collectTypeVars(kwt);
          }
       }
       
       // TODO: take different bounds into account
       if(!(dataTypeVars <= allFieldTypeVars)){
          frb.reportError(v, "Unbound type parameter <fmt(dataTypeVars - allFieldTypeVars)>");
       }
       consType = acons(adtType, consName, fields, kwFields);
       frb.define(scope, consName, constructorId(), v.name, defType(consType));
    }
    return decl;
}
