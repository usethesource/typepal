module rascal::Declaration

extend typepal::TypePal;

import lang::rascal::\syntax::Rascal;
import rascal::ConvertType;
//import lang::rascal::types::AbstractName;
import rascal::ATypeUtils;

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
    <msgs, varType> = convertType(varDecls.\type);
    for(msg <- msgs){
        if(msg is error) frb.reportError(msg.msg, varDecls.\type);
        if(msg is warning) frb.reportWarning(msg.msg, varDecls.\type);
    }
    
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
void() makeReturnRequirement(Expression expr, AType retType)
    = () { 
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
    <msgs, retType> = convertType(signature.\type);
    for(msg <- msgs){
        if(msg is error) frb.reportError(msg.msg, signature.\type);
        if(msg is warning) frb.reportWarning(msg.msg, signature.\type);
    }
    kwFormals = [];
    
    if(params.keywordFormals is \default){
        kwFormals = getKeywordFormals(params.keywordFormals.keywordFormalList, decl, frb);
    }
    dt = defType(formals, AType() { return afunc(retType, atypeList([typeof(f) | f <- formals]), kwFormals); });
    dt.vis=visibility;  // TODO: Cannot be set directly, bug in interpreter?
    frb.define(scope, "<fname>", functionId(), fname, dt);
    if(decl is \default){
        for(Expression expr <- getReturnExpressions(decl)){
            frb.requireEager("return type", expr, [expr], makeReturnRequirement(expr, retType));     
        }
    } else
    if(decl is expression){
        frb.requireEager("return type", decl.expression, [decl.expression], makeReturnRequirement(decl.expression, retType));
    } else
    if(decl is conditional){
        frb.requireEager("return type", decl.expression, [decl.expression], makeReturnRequirement(decl.expression, retType));
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

lrel[AType, str, Expression] getKeywordFormals({KeywordFormal  "," }+ keywordFormalList, Tree scope, FRBuilder frb){    
    return 
        for(KeywordFormal kwf <- keywordFormalList){
            <msgs, fieldType> = convertType(kwf.\type);
            for(msg <- msgs){
                if(msg is error) frb.reportError(msg.msg, kwf.\type);
                if(msg is warning) frb.reportWarning(msg.msg, kwf.\type);
            }
            fieldName = "<kwf.name>";
            defaultExp = kwf.expression;
            frb.define(scope, fieldName, formalId(), kwf.name, defType(fieldType));
            append <fieldType, fieldName, defaultExp>;
        }
}

Tree define (decl: (Declaration) `<Tags tags> <Visibility visibility> data <UserType user> <CommonKeywordParameters commonKeywordParameters> = <{Variant "|"}+ variants> ;`, Tree scope, FRBuilder frb){
    adtName = "<user.name>";
    
    commonKwFields = [];
    if(commonKeywordParameters is present){
        commonKwFields = getKeywordFormals(commonKeywordParameters.keywordFormalList, decl, frb);
    }
    adtType = aadt(adtName, [], commonKwFields);
    frb.define(scope, adtName, dataId(), user.name, defType(adtType));
    
    for(Variant v <- variants){
        consName = "<v.name>";
        fields = 
            for(TypeArg ta <- v.arguments){
                <msgs, fieldType> = convertType(ta.\type);
                for(msg <- msgs){
                    if(msg is error) frb.reportError(msg.msg, ta.\type);
                    if(msg is warning) frb.reportWarning(msg.msg, ta.\type);
                }
                fieldName = ta has name ? "<ta.name>" : "";
                append <fieldType, fieldName>;
            }
    
       kwFields = [];
       if(v.keywordArguments is \default){
          kwFields += getKeywordFormals(v.keywordArguments.keywordFormalList, decl, frb);
       }
       consType = acons(adtType, consName, fields, kwFields);
       frb.define(scope, consName, constructorId(), v.name, defType(consType));
    }
    return decl;
}
