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

void collect(m: (Module) `<Header header> <Body body>`, FRBuilder frb){
    frb.define("<header.name>", moduleId(), m, defType(amodule("<header.name>")));
    frb.enterScope(moduleScope(), m);
        collectParts(m, frb);
    frb.leaveScope(moduleScope(), m);
}

void collect(imp: (Import) `import <ImportedModule m> ;`, FRBuilder frb){
    frb.use_ref(m.name, {moduleId()}, importPath());
}

void collect(imp: (Import) `extend <ImportedModule m> ;`, FRBuilder frb){
    frb.use_ref(m.name, {moduleId()}, extendPath());
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
         
void collect(varDecls: (Declaration) `<Tags tags> <Visibility visibility> <Type \type> <{Variable ","}+ variables> ;`, FRBuilder frb){
    vis = getVis(varDecls.visibility);
    if(vis == defaultVis()){
        vis = privateVis();
    }
    varType = convertType(varDecls.\type, frb);
    
    for(var <- variables){
        frb.define("<var.name>", variableId(), var.name, defType(varType, vis=vis));
        if(var is initialized){
            frb.require("variable initialization", var.initial, [], makeVarInitRequirement(var.initial, varType));
        }
    }
    collectParts(varDecls, frb);
}

void() makeReturnRequirement(Tree expr, AType retType, list[Pattern] formals, set[str] kwTypeVars)
       = () { typeVarsInParams = {*collectTypeVars(typeof(f)) | f <- formals} + kwTypeVars;
              typeVarsInReturn = collectTypeVars(retType);
              if(!(typeVarsInReturn <= typeVarsInParams)){
                reportError(signature.\type, "Unbound type variable in return type");
              }
            
              if(isFullyInstantiated(typeof(expr))){
                subtype(typeof(expr), retType, onError(expr, "Return type should be subtype of <fmt(retType)>, found <fmt(expr)>"));
              } else {
              if(!unify(typeof(expr), retType)){
                 subtype(typeof(expr), retType, onError(expr, "Return type should be subtype of <fmt(retType)>, found <fmt(expr)>"));
              }
           }
         };
             
void collect(FunctionDeclaration decl, FRBuilder frb){
    visibility = getVis(decl.visibility);
    if(visibility == defaultVis()){
        visibility = publicVis();
    }
    signature = decl.signature;
    fname = signature.name;
    ftype = frb.newTypeVar();
    dt = defType([], AType() { return typeof(ftype); });
    dt.vis=visibility;  // TODO: Cannot be set directly, bug in interpreter?
    frb.define("<fname>", functionId(), fname, dt);
    
    frb.enterScope(functionScope(), decl);
        params = signature.parameters;
        formals = [pat | Pattern pat <- params.formals.formals];
        
        // Take care of single variable patterns
        defineSingleVarsInFormals(formals, frb);
        
        retType = convertType(signature.\type, frb);
        kwFormals = [];
        
        if(params.keywordFormals is \default){
            kwFormals = getKeywordFormals(params.keywordFormals.keywordFormalList, frb);
        }
        
        frb.require("define return type", decl, [],
            (){ unify(ftype, afunc(retType, atypeList([typeof(f) | f <- formals]), kwFormals)); });
        
        kwTypeVars = {*collectTypeVars(kwf.fieldType) | kwf <- kwFormals};
        frb.setScopeInfo(<retType, formals, kwTypeVars>);
        
        frb.require("bound type variables", decl, formals,
            () { typeVarsInParams = {*collectTypeVars(typeof(f)) | f <- formals} + kwTypeVars;
                 typeVarsInReturn = collectTypeVars(retType);
                 if(!(typeVarsInReturn <= typeVarsInParams)){
                    reportError(signature.\type, "Unbound type variable in return type");
                 }
            });
        //if(decl is \default){
        //    for(Expression expr <- getReturnExpressions(decl)){
        //        frb.requireEager("check return type", expr, [expr], makeReturnRequirement(expr, retType, formals, kwTypeVars));     
        //    }
        //} else
        
        if(decl is expression || decl is conditional){
            frb.requireEager("return type", decl.expression, [decl.expression], makeReturnRequirement(decl.expression, retType, formals, kwTypeVars));
        } 
        if(decl is conditional){
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
        collectParts(decl, frb);
        
    frb.leaveScope(functionScope(), decl);
}

void defineSingleVarsInFormals(list[Pattern] pats, FRBuilder frb){
    for(pat <- pats){
        if(namePat: (Pattern) `<QualifiedName name>` := pat){
            frb.atomicFact(pat, avalue());
            frb.define("<name>", formalId(), name, defLub([], AType() { return avalue(); }));
        }
        if(splicePat: (Pattern) `*<QualifiedName name>` := pat || splicePat: (Pattern) `<QualifiedName name>*` := pat){            
            frb.atomicFact(pat, avalue());
            frb.define("<name>", formalId(), name, defLub([], AType() { return alist(avalue()); }));
        }
        if(splicePlusPat: (Pattern) `+<QualifiedName name>` := pat){
            frb.atomicFact(pat, avalue());
            frb.define("<name>", formalId(), name, defLub([], AType() { return alist(avalue()); }));
        }
    }
}

list[Keyword] getKeywordFormals({KeywordFormal  "," }+ keywordFormalList, FRBuilder frb){    
    return 
        for(KeywordFormal kwf <- keywordFormalList){
            fieldType = convertType(kwf.\type, frb);
            fieldName = "<kwf.name>";
            defaultExp = kwf.expression;
            frb.define(fieldName, formalId(), kwf.name, defType(fieldType));
            append <fieldType, fieldName, defaultExp>;
        }
}

void collect(stat: (Statement) `return <Statement statement>`, FRBuilder frb){  
    <found, scope, scopeInfo> = frb.getScopeInfo(functionScope());
    if(!found){
        frb.reportError(stat, "Return outside a function declaration");
        return;
    }
    if(<AType retType, list[Pattern] formals, set[str] kwTypeVars> := scopeInfo){
       frb.requireEager("return type", stat, [statement], makeReturnRequirement(statement, retType, formals, kwTypeVars));
    } else {
        throw "Inconsistent info from function scope: <scopeInfo>";
    }
    collectParts(stat, frb);
}


void collect (decl: (Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters>;`, FRBuilder frb)
    = dataDeclaration(decl, [], frb);

void collect (decl: (Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters> = <{Variant "|"}+ variants> ;`, FRBuilder frb)
    = dataDeclaration(decl, [v | v <- variants], frb);

void dataDeclaration(Declaration decl, list[Variant] variants, FRBuilder frb){
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
        commonKwFields = getKeywordFormals(commonKeywordParameters.keywordFormalList, frb);
    }
    adtType = aadt(adtName, dataTypeVars0, commonKwFields);
    frb.define(adtName, dataId(), userType.name, defType(adtType));
    
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
          kwFields += getKeywordFormals(v.keywordArguments.keywordFormalList, frb);
          for(<kwt, kwn,kwd> <- kwFields){
              allFieldTypeVars += collectTypeVars(kwt);
          }
       }
       
       // TODO: take different bounds into account
       if(!(dataTypeVars <= allFieldTypeVars)){
          frb.reportError(v, "Unbound type parameter <fmt(dataTypeVars - allFieldTypeVars)>");
       }
       consType = acons(adtType, consName, fields, kwFields);
       frb.define(consName, constructorId(), v.name, defType(consType));
    }

}
