@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module examples::pascal::Checker

import examples::pascal::Syntax;

extend analysis::typepal::TypePal;

import List;
import Set;
import String;

// ----  IdRoles, PathLabels and AType ------------------- 

data IdRole
    = fileId()
    | constantId()
    | typeId()
    | recordId()
    | fieldId()
    | tagId()
    | variableId()
    | formalId()
    | labelId()
    | functionId()
    | nullaryFunctionId()
    | procedureId()
    ;
    
data PathRole
    = withPath()
    ;

data AType
    = booleanType()
    | integerType()
    | realType()
    | stringType()
    | charType()
    | textType()
    | scalarType(list[str] elems)
    | subrangeType(AType associatedType)
    | arrayType(AType indexType, AType elemType, bool packed = false)
    | setType(AType elemType, bool packed = false)
    | voidType()
    | fileType(AType elemType, bool packed = false)
    | pointerType(AType elemType)
    | anyPointerType()
    | functionType(AType argTypes, AType resType)
    | anyFunctionType(AType resType)
    | procedureType(AType argTypes)
    | anyProcedureType()
    | recordType(str rname, bool packed = false)
    | labelType()
    ;
    
AType stringType() = arrayType(subrangeType(integerType()), charType(), packed=true);

bool isSimpleType(booleanType())                        = true;
bool isSimpleType(integerType())                        = true;
bool isSimpleType(realType())                           = true;
bool isSimpleType(charType())                           = true;
bool isSimpleType(scalarType(list[str] elems))          = true;
default bool isSimpleType(AType t)                      = false;

bool isScalarType(booleanType())                        = true;
bool isScalarType(integerType())                        = true;
bool isScalarType(charType())                           = true;
bool isScalarType(scalarType(list[str] elems))          = true;
bool isScalarType(subrangeType(AType associatedType))   = true;
default bool isScalarType(AType t)                      = false;

AType elimSubrangeType(AType t) = visit(t) { case subrangeType(AType t1) => t1 };

str prettyAType(booleanType())                                     = "boolean";
str prettyAType(integerType())                                     = "integer";
str prettyAType(realType())                                        = "real";
str prettyAType(charType())                                        = "char";
str prettyAType(textType())                                        = "text";
    
str prettyAType(scalarType(list[str] elems))                       = "(<intercalate(", ", elems)>)";
str prettyAType(subrangeType(AType associatedType))                = "subrange of <prettyAType(associatedType)>";
str prettyAType(tp: arrayType(AType indexType, AType elemType))    = tp == stringType() ? "string" : (tp.packed ? "packed " : "") + "array <prettyAType(indexType)> of <prettyAType(elemType)>";
str prettyAType(tp: setType(AType elemType))                       = (tp.packed ? "packed " : "") + "set of <prettyAType(elemType)>";
str prettyAType(tp: fileType(AType elemType))                      =  (tp.packed ? "packed " : "") + "file of <prettyAType(elemType)>";
str prettyAType(pointerType(AType elemType))                       = "^" + prettyAType(elemType);
str prettyAType(procedureType(AType argTypes))                     = "procedure (<prettyAType(argTypes)>)";
str prettyAType(functionType(AType argTypes, AType resType))       = "function (<prettyAType(argTypes)>) : <prettyAType(resType)>";
str prettyAType(tp: recordType(str rname))                         =  (tp.packed ? "packed " : "") + "record " + rname;

// ---- isSubType
    
bool pascalIsSubType(AType t, t) = true;

bool pascalIsSubType(voidType(), t) = true;

bool pascalIsSubType(integerType(), realType()) = true;

bool pascalIsSubType(atypeList(list[AType] elems1), atypeList(list[AType] elems2))
    = size(elems1) == size(elems2) && all(int i <- index(elems1), pascalIsSubType(elems1[i], elems2[i]));


bool pascalIsSubType(subrangeType(AType associatedType), AType other)
    = pascalIsSubType(associatedType, other);
     
bool pascalIsSubType(AType other, subrangeType(AType associatedType))
    = pascalIsSubType(other, associatedType);
    
bool pascalIsSubType(a1: arrayType(AType indexType1, AType elementType1), a2: arrayType(AType indexType2, AType elementType2))
    = indexType1 == indexType1 && pascalIsSubType(elementType1, elementType2);
    
//bool pascalIsSubType(charType(), arrayType(subrangeType(integerType()), charType()))
//    = true;
    
//bool pascalIsSubType(charType(), integerType())
//    = true;
    
bool pascalIsSubType(integerType(), charType())
    = true;
    
bool pascalIsSubType(setType(AType elemType1), setType(AType elemType2)) = pascalIsSubType(elemType1, elemType2);
    
bool pascalIsSubType(arrayType(subrangeType(integerType()), charType()), charType())
    = true;

bool pascalIsSubType(pointerType(AType t1), pointerType(AType t2))
    = pascalIsSubType(t1, t2);

bool pascalIsSubType(anyPointerType(), pointerType(AType t2))
    = true;

bool pascalIsSubType(functionType(args, AType resultType1), anyFunctionType(AType resultType2))
    = pascalIsSubType(resultType2, resultType1);
    
bool pascalIsSubType(AType atype, functionType(_, atype)) = true;  // for assignment to function id

default bool pascalIsSubType(AType atype1, AType atype2) = false;
 
Tree mkTree(int n) = [Identifier] "<for(int i <- [0 .. n]){>x<}>"; // A unique tree

void pascalPreCollectInitialization(Tree tree, Collector c){
    c.define("true",    constantId(),   mkTree(1), defType(booleanType()));
    c.define("false",   constantId(),   mkTree(2), defType(booleanType()));
    c.define("writeln", procedureId(),  mkTree(3), defType(procedureType(atypeList([]))));
    c.define("write",   procedureId(),  mkTree(4), defType(procedureType(atypeList([]))));
    c.define("odd",     functionId(),   mkTree(5), defType(functionType(atypeList([integerType()]), booleanType())));
    c.define("abs",     functionId(),   mkTree(6), defType(functionType(atypeList([integerType()]), integerType())));
    c.define("sqr",     functionId(),   mkTree(7), defType(functionType(atypeList([integerType()]), integerType())));
    c.define("sin",     functionId(),   mkTree(8), defType(functionType(atypeList([realType()]), realType())));
    c.define("cos",     functionId(),   mkTree(9), defType(functionType(atypeList([realType()]), realType())));
    c.define("arctan",  functionId(),   mkTree(10), defType(functionType(atypeList([realType()]), realType())));
    c.define("exp",     functionId(),   mkTree(11), defType(functionType(atypeList([realType()]), realType())));
    c.define("ln",      functionId(),   mkTree(12), defType(functionType(atypeList([realType()]), realType())));
    c.define("sqrt",    functionId(),   mkTree(13), defType(functionType(atypeList([realType()]), realType())));
    c.define("round",   functionId(),   mkTree(14), defType(functionType(atypeList([realType()]), integerType())));
    c.define("readln",  procedureId(),  mkTree(15), defType(procedureType(atypeList([]))));
    c.define("read",    procedureId(),  mkTree(16), defType(procedureType(atypeList([]))));
    c.define("new",     procedureId(),  mkTree(17), defType(procedureType(atypeList([]))));
    
    c.define("boolean", typeId(),       mkTree(18), defType(booleanType()));
    c.define("integer", typeId(),       mkTree(19), defType(integerType()));
    c.define("real",    typeId(),       mkTree(20), defType(realType()));
    c.define("string",  typeId(),       mkTree(21), defType(stringType()));
    c.define("text",    typeId(),       mkTree(22), defType(textType()));
    c.define("any",     typeId(),       mkTree(23), defType(anyPointerType()));
    c.define("char",    typeId(),       mkTree(24), defType(charType()));
    
    c.define("eof",    nullaryFunctionId(),   
                                        mkTree(25), defType(booleanType()));
    c.define("eoln",   nullaryFunctionId(),   
                                        mkTree(26), defType(booleanType()));
    c.define("trunc",  functionId(),    mkTree(27), defType(functionType(atypeList([realType()]), integerType())));
    c.define("ord",    functionId(),    mkTree(29), defType(functionType(atypeList([integerType()]), charType())));
    c.define("chr",    functionId(),    mkTree(30), defType(functionType(atypeList([charType()]), integerType())));
    c.define("succ",   functionId(),    mkTree(31), defType(functionType(atypeList([integerType()]), integerType())));
    c.define("pred",   functionId(),    mkTree(32), defType(functionType(atypeList([integerType()]), integerType())));
}

tuple[list[str] typeNames, set[IdRole] idRoles] pascalGetTypeNamesAndRole(recordType(str name)){
    return <[name], {recordId()}>;
}

default tuple[list[str] typeNames, set[IdRole] idRoles] pascalGetTypeNamesAndRole(AType t){
    return <[], {}>;
}

// Configure TypePal, after the above preparations

TypePalConfig pascalConfig() =
    tconfig(isSubType           = pascalIsSubType,
            getTypeNamesAndRole = pascalGetTypeNamesAndRole
           );

// ====  Collect rules for Pascal =============================================

// Program

void collect(current: (Program) `<ProgramHeading programHeading> <Block block> .`, Collector c){
    collect(programHeading, block, c);
} 

void collect(ProgramHeading ph, Collector c) {
    for(fid <- ph.fileIdentifiers){
        c.define("<fid>", fileId(), fid, defType(fileType(textType())));
    }
}

// Block

void collect(current: (Block) `<LabelDeclarationPart? labelDeclarationPart> <ConstantDefinitionPart? constantDefinitionPart> <TypeDefinitionPart? typeDefinitionPart><VariableDeclarationPart? variableDeclarationPart> <ProcedureAndFunctionDeclarationPart? procedureAndFunctionDeclarationPart> <StatementPart statementPart>`, Collector c) {
   
   for(neLabelDeclarationPart <- labelDeclarationPart) collect(neLabelDeclarationPart, c);
   for(neConstantDefinitionPart <- constantDefinitionPart) collect(neConstantDefinitionPart, c);
   for(neTypeDefinitionPart <- typeDefinitionPart) collect(neTypeDefinitionPart, c);
   for(neVariableDeclarationPart <- variableDeclarationPart) collect(neVariableDeclarationPart, c);
   for(neProcedureAndFunctionDeclarationPart <- procedureAndFunctionDeclarationPart) collect(neProcedureAndFunctionDeclarationPart, c);
   collect(statementPart, c);
   //collect(labelDeclarationPart, 
   //        constantDefinitionPart, 
   //        typeDefinitionPart, 
   //        variableDeclarationPart, 
   //        procedureAndFunctionDeclarationPart,
   //        statementPart, c);
}
// Labels

void collect(current: (LabelDeclarationPart) `label <{Label ","}+  labels> ;`, Collector c) {
    for(lab <- labels){
        c.define("<lab>", labelId(), lab, defType(labelType()));
    }
}

// Constants

void collect(current: (ConstantDefinitionPart) `const <{ConstantDefinition ";"}+ constantDefs> ;`, Collector c){
    collect(constantDefs, c);
}

void collect(current: (ConstantDefinition) `<Identifier id> = <Constant constant>`, Collector c) {
   c.define("<id>", constantId(), id, defType(constant));
   collect(constant, c);
}

void collect(current: (Constant) `<UnsignedInteger unsignedInteger>`, Collector c){
    c.fact(current, integerType());
}

void collect(current: (Constant) `<UnsignedReal unsignedReal>`, Collector c){
    c.fact(current, realType());
}

void collect(current: (Constant) `<Sign sign> <UnsignedNumber unsignedNumber>`, Collector c){
    c.fact(current, unsignedNumber);
    collect(unsignedNumber, c);
}

void collect(current: (Constant) `<ConstantIdentifier constantIdentifier>`, Collector c){
    c.use(constantIdentifier, {constantId()});
}

void collect(current: (Constant) `<Sign sign> <ConstantIdentifier constantIdentifier>`, Collector c){
    c.use(constantIdentifier, {constantId()});
}

AType getStringType(String string){
    return (size("<string>") == 3 || "<string>" == "\'\'") ? charType() // 2 quotes + single char (or escaped quote)
                                                     : stringType();
}

void collect(current: (Constant) `<String string>`, Collector c){
    c.fact(current, getStringType(string));
}

void collect(current: (UnsignedConstant) `nil`, Collector c){
    c.fact(current, anyPointerType());
}

void collect(current: (UnsignedNumber) `<UnsignedInteger unsignedInteger>`, Collector c){
    c.fact(current, integerType());
}

void collect(current: (UnsignedNumber) `<UnsignedReal unsignedReal>`, Collector c){
    c.fact(current, realType());
}

void collect(String string, Collector c){
    c.fact(string, getStringType(string));
}

void collect(ConstantIdentifier identifier, Collector c){
    c.use(identifier, {constantId()});
}

//  Types

void collect(current: (TypeDefinitionPart) `type <{TypeDefinition ";"}+ typeDefs> ;`, Collector c){
    collect(typeDefs, c);
}

void collect(current: (TypeDefinition) `<Identifier id> = <Type rtype>`, Collector c) {
    c.define("<id>", typeId(), id, defType(rtype));
    collect(rtype, c);
}

// scalar type

void collect(current: (ScalarType) `(  <{Identifier ","}+ ids> )`, Collector c){
    st = scalarType(["<id>" | id <- ids]);
    c.fact(current, st);
    for(id <- ids){
        c.define("<id>", constantId(), id, defType(st));
    }
}

// subrange type

void collect(current: (SubrangeType) `<Constant from> .. <Constant to>`, Collector c){
    c.requireEqual(from, to, error(current, "Subrange type requires lower and upper bound of equal type, found %t and %t", from, to));
    c.calculate("subrange", current, [from, to],
        AType(Solver s) { return subrangeType(s.getType(from)); });
    collect(from, to, c);
}

void collect(TypeIdentifier identifier, Collector c){
    c. use(identifier, {typeId()});
}

// array type
void collect(current: (ArrayType) `array [ <{SimpleType ","}+ indexTypes> ] of <Type rtype>`, Collector c){
    index_types = [itp | itp <- indexTypes];
    c.calculate("array type", current, index_types + rtype,
        AType(Solver s){
            return arrayType(atypeList([s.getType(itp) | itp <- index_types]), s.getType(rtype));
        });
    collect(indexTypes, rtype, c);
}

// record type

void collect(current: (RecordType) `record <FieldList fieldList> end`, Collector c){
    recordName = "<getLoc(current)>"; //create an artifical name for the record.
    c.define(recordName, recordId(), current, defType(recordType(recordName)));
    c.enterScope(current);
        collect(fieldList, c);   
    c.leaveScope(current);
} 

void collect(current:(FieldList) `<FixedPart fixedPart> ; <VariantPart variantPart>`, Collector c){
    collect(fixedPart, variantPart, c);
}

void collect(current: (RecordSection) `<{FieldIdentifier ","}+ fieldIdentifiers> : <Type rtype>`, Collector c){
    for(fid <- fieldIdentifiers){
        c.define("<fid>", fieldId(), fid, defType(rtype));
    }
   collect(rtype, c);
}

void collect(current: (VariantPart) `case <TagField tagField> <TypeIdentifier ctype> of <{Variant ";"}+ variantList>`, Collector c){
    c.define("<tagField>", tagId(), tagField, defType(ctype));
    //TODO: check that all case labels are complete and are compatible with ctype
    collect(ctype, variantList, c);
} 

void collect(current: (Variant) `<{CaseLabel ","}+ caseLabels> : ( <FieldList fieldList> )`, Collector c){
    collect(caseLabels, fieldList, c);
}

// set type

void collect(current: (SetType) `set of <SimpleType simpleType>`, Collector c){
    c.calculate("set type", current, [simpleType],
        AType(Solver s){
            tp = s.getType(simpleType);
            if(subrangeType(associatedType) := tp) tp = associatedType;
            return setType(s.getType(simpleType));
        });
    collect(simpleType, c);
}  

// file type

void collect(current: (FileType) `file of <Type typ>`, Collector c){
    c.calculate("file type", current, [typ], AType(Solver s){ return fileType(s.getType(typ)); });
    collect(typ, c);
}  

// pointer type

void collect(current: (Type) `^ <TypeIdentifier identifier>`, Collector c){
    c.calculate("pointer type", current, [identifier],
        AType(Solver s){
            return pointerType(s.getType(identifier));
        });
    collect(identifier, c);
}

// variable declaration

void collect(current: (VariableDeclarationPart) `var <{VariableDeclaration ";"}+ variableDeclarations> ;`, Collector c){
    collect(variableDeclarations, c);
}

void collect(current: (VariableDeclaration) `<{Identifier ","}+ ids> : <Type typ>`, Collector c) {
    for(Identifier id <- ids){
        c.define("<id>", variableId(), id, defType(typ));
    }
    collect(typ, c);
}

// procedure and function declaration

void collect(current: (ProcedureOrFunctionDeclaration) `<ProcedureDeclaration procedureDecl> ;`, Collector c){
    collect(procedureDecl, c);
}

void collect(current: (ProcedureOrFunctionDeclaration) `<FunctionDeclaration functionDecl> ;`, Collector c){
    collect(functionDecl, c);
}

void collect(current: (FormalParameterSection) `<{Identifier ","}+ ids> : <Type rtype>`, Collector c){
    for(id <- ids){
        c.define("<id>", formalId(), id, defType(rtype));
    }
    c.calculate("parameter group", current, [rtype],
        AType(Solver s) {
            return atypeList([ s.getType(rtype) | id <- ids ]);
        });
    collect(rtype, c);
}

void collect(current: (FormalParameterSection) `var <{Identifier ","}+ ids> : <Type rtype>`, Collector c){
    for(id <- ids){
        c.define("<id>", variableId(), id, defType(rtype));
    }
    c.calculate("var parameter group", current, [rtype],
        AType(Solver s) {
            return atypeList([ s.getType(rtype) | id <- ids ]);
        });
    collect(rtype, c);
}

void collect(current: (FormalParameterSection) `function <{Identifier ","}+ ids> : <Type rtype>`, Collector c){
    for(id <- ids){
        c.define("<id>", functionId(), id, defType([rtype], AType(Solver s) { return anyFunctionType(s.getType(rtype)); }));
    }
    c.calculate("function parameter group", current, [rtype],
        AType(Solver s) {
            return atypeList([ anyFunctionType(s.getType(rtype)) | id <- ids ]);
        });
    collect(rtype, c);
}

void collect(current: (FormalParameterSection) `procedure <{Identifier ","}+ ids>`, Collector c){
    for(id <- ids){
        c.define("<id>", procedureId(), id, defType(anyProcedureType()));
    }
    c.fact(current, atypeList([ anyProcedureType() | id <- ids ]));
}

void collect({FormalParameterSection ";"}+ formals, Collector c){ 
    fps_list = [fps | fps <- formals];

    c.calculate("formal parameter sections", formals, fps_list,
        AType(Solver s){
            formalTypes = [];
            for(fps <- formals){
                if(atypeList(tps) := s.getType(fps)){
                    formalTypes += tps;
                }
            }
            return atypeList(formalTypes);
    });
    collect(fps_list, c);      
}

void collect(FunctionDeclaration fd, Collector c){
    hd = fd.functionHeading;
    outer = c.getScope();
    c.enterScope(fd);
        if(hd has formals){
          c.defineInScope(outer, "<hd.id>", functionId(), hd.id, 
                   defType([hd.formals, hd.rtype], AType(Solver s){ return functionType(s.getType(hd.formals), s.getType(hd.rtype)); }));
          collect(hd.formals, hd.rtype, c);
        } else {
           c.defineInScope(outer, "<hd.id>", functionId(), hd.id, 
                    defType([hd.rtype], AType(Solver s) { return functionType(atypeList([]), s.getType(hd.rtype)); }));
           collect(hd.rtype, c);
        }
    c.leaveScope(fd);
}

void collect(ProcedureDeclaration pd, Collector c){
    hd = pd.procedureHeading;
    outer = c.getScope();
    c.enterScope(pd);
        if(hd has formals){
           c.defineInScope(outer, "<hd.id>", procedureId(), hd.id, defType([hd.formals],  AType(Solver s) { return procedureType(s.getType(hd.formals)); }));
           collect(hd.formals, c); 
        } else {
           c.defineInScope(outer, "<hd.id>", procedureId(), hd.id, defType(procedureType(atypeList([])))); 
        }
    c.leaveScope(pd);
}

// Statement

void collect(current: (Statement) `<Label label>: <UnlabelledStatement us>`, Collector c) {
    c.define("<label>", labelId(), label, defType(labelType()));
    collect(us, c);
}

// assignment statement

void collect(current: (AssignmentStatement) `<Variable var> := <Expression exp>`, Collector c){
    c.requireSubType(exp, var, error(current, "Incorrect assignment, expected subtype of %t, found %t", var, exp));
    collect(var, exp, c);
}

void collect(e: (EntireVariable) `<EntireVariable var>`, Collector c){
     c.use(var, {formalId(), variableId(), constantId(), fieldId(), nullaryFunctionId(), functionId()});
}

void collect(current: (ReferencedVariable) `<Variable var>^`, Collector c){
     c.calculate("referenced variable <current>", current, [var],
         AType(Solver s) {
              if(pointerType(tau1) := s.getType(var)){ 
                return tau1;
              } else {
                s.report(error(var, "Pointer type required, found %t", var));
                return voidType();
              }
            });
     collect(var, c);
}

void collect((TypeIdentifier) `<TypeIdentifier tvar>`, Collector c){
     c.use(tvar, {typeId()});
}

// expression

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
    c.fact(current, exp);
    collect(exp, c);
}

// Operator overloading

void overloadRelational(Expression e, str op, Expression exp1, Expression exp2, Collector c){
    c.calculate("relational operator `<op>`", e,  [exp1, exp2], 
        AType(Solver s) {
              t1 = elimSubrangeType(s.getType(exp1));
              t2 = elimSubrangeType(s.getType(exp2));
              
              switch([t1, t2]){
              case [booleanType(), booleanType()]: return booleanType();
              case [integerType(), integerType()]: return booleanType();
              case [integerType(), realType()]: return booleanType();
              case [realType(), integerType()]: return booleanType();
              case [realType(), realType()]: return booleanType();
              case [scalarType(tau1), scalarType(tau1)]: return booleanType();
              //case [subrangeType(integerType()), realType()]: return booleanType();
              //case [realType(), subrangeType(integerType())]: return booleanType();
              //case [tau1, subrangeType(tau1)]: return booleanType();
              //case [subrangeType(tau1), tau1]: return booleanType();
              //case [subrangeType(tau1), subrangeType(tau1)]: return booleanType();
              case [tau1, setType(tau1)]: return booleanType();
              case [setType(tau1), setType(tau1)]: return booleanType();
              case [setType(voidType()), setType(tau1)]: return booleanType();
              case [setType(tau1), setType(voidType())]: return booleanType();
              case [ tau1, tau1 ]: return booleanType();
              default: {
                 if(op == "\<\>"){
                    switch([t1, t2]){
                        case [pointerType(tau1), pointerType(tau1)]: return booleanType();
                        case [pointerType(anyPointerType()), pointerType(tau1)]: return booleanType();
                        case [pointerType(tau1), pointerType(anyPointerType())]: return booleanType();
                    }
                 }
                 s.report(error(e, "%q not defined on %t and %t", op, exp1, exp2)); 
                 return voidType();
               }
            }
        });
    collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> = <Expression exp2>`, Collector c)
    = overloadRelational(current, "=", exp1, exp2, c);

void collect(current: (Expression) `<Expression exp1> \<\> <Expression exp2>`, Collector c)
    = overloadRelational(current, "\<\>", exp1, exp2, c);

void collect(current: (Expression) `<Expression exp1> \< <Expression exp2>`, Collector c)
    = overloadRelational(current, "\<", exp1, exp2, c);
    
void collect(current: (Expression) `<Expression exp1> \<= <Expression exp2>`, Collector c)
    = overloadRelational(current, "\<=", exp1, exp2, c); 
    
void collect(current: (Expression) `<Expression exp1> \>= <Expression exp2>`, Collector c)
    = overloadRelational(current, "\>=", exp1, exp2, c); 
     
void collect(current: (Expression) `<Expression exp1> \> <Expression exp2>`, Collector c)
    = overloadRelational(current, "\>", exp1, exp2, c);           

void collect(current: (Expression) `<Expression exp1> in <Expression exp2>`, Collector c){
    c.calculate("relational operator", current, [exp1, exp2], 
        AType(Solver s) { 
            switch([s.getType(exp1), s.getType(exp2)]){
                case [tau1, setType(tau2)]: if(pascalIsSubType(tau1, tau2)) return booleanType(); else fail;
                default:
                    s.report(error(current, "`in` not defined on %t and %t", exp1, exp2));  
            }
        });
     collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> * <Expression exp2>`, Collector c){
    c.calculate("multiplication", current, [exp1, exp2], 
        AType(Solver s) { 
            t1 = elimSubrangeType(s.getType(exp1));
            t2 = elimSubrangeType(s.getType(exp2));
            switch([t1, t2]){
              case [integerType(), integerType()]: return integerType();
              case [integerType(), realType()]: return realType();
              case [realType(), integerType()]: return realType();
              case [realType(), realType()]: return realType();
              //case [subrangeType(integerType()), realType()]: return realType();
              //case [realType(), subrangeType(integerType())]: return realType();
              //case [subrangeType(tau1), tau1]: return tau1;
              //case [subrangeType(tau1), subrangeType(tau1)]: return tau1;
              case [setType(tau1), setType(tau1)]: return setType(tau1);
              default: {
                   s.report(error(current, "`*` not defined on %t and %t", exp1, exp2));
                   return voidType();
                 }
            }
        }); 
    collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> / <Expression exp2>`, Collector c){
    c.calculate("division", current, [exp1, exp2], 
        AType(Solver s) {
            switch([s.getType(exp1), s.getType(exp2)]){
               case [integerType(), integerType()]: return realType();
               case [integerType(), realType()]: return realType();
               case [realType(), integerType()]: return realType();
               case [realType(), realType()]: return realType();
               default:
                    s.report(error(current, "`/` not defined on %t and %t", exp1, exp2));
             }
         });
    collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> div <Expression exp2>`, Collector c){
    c.calculate("div", current, [exp1, exp2],
        AType(Solver s) {
            s.requireEqual(exp1, integerType(), error(exp1, "Left argument of `div` should be `integer`, found %t", exp1));
            s.requireEqual(exp2, integerType(), error(exp2, "Right argument of `div` should be `integer`, found %t", exp2));
            return integerType();
        });  
     collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> mod <Expression exp2>`, Collector c){
    c.calculate("mod", current, [exp1, exp2], 
        AType(Solver s) {
            s.requireEqual(exp1, integerType(), error(exp1, "Left argument of `mod` should be `integer`, found %t", exp1));
            s.requireEqual(exp2, integerType(), error(exp2, "Right argument of `mod` should be `integer`, found %t", exp2));
            return integerType();
        });  
     collect(exp1, exp2, c);
}

void collect(current: (Expression) `<Expression exp1> and <Expression exp2>`, Collector c){
    c.calculate("and", current, [exp1, exp2], 
        AType(Solver s) { 
            s.requireEqual(exp1, booleanType(), error(exp1, "Left argument of `and` should be `boolean`, found %t", exp1));
            s.requireEqual(exp2, booleanType(), error(exp2, "Right argument of `and` should be `boolean`, found %t", exp2));
            return booleanType();
        }); 
     collect(exp1, exp2, c); 
}

void collect(current: (Expression) `not <Expression exp>`, Collector c){
    c.calculate("not", current, [exp], 
        AType(Solver s) { 
            s.requireEqual(exp, booleanType(), error(current, "Argument of `not` should be `boolean`, found %t", exp));
            return booleanType();
        });
     collect(exp, c);
}

void collect(current: (Expression) `<Sign sign> <Expression exp>`, Collector c){
     c.fact(current, exp);
     collect(sign, exp, c);
}

void overloadAdding(Expression e, str op, Expression exp1, Expression exp2, Collector c){
 c.calculate("adding operator", e, [exp1, exp2], 
     AType(Solver s) { 
        t1 = elimSubrangeType(s.getType(exp1));
        t2 = elimSubrangeType(s.getType(exp2));
        switch([t1, t2]){
           case [integerType(), integerType()]: return integerType();
           case [integerType(), realType()]: return realType();
           case [realType(), integerType()]: return realType();
           case [realType(), realType()]: return realType();
           //case [tau1, subrangeType(tau1)]:  return tau1;
           //case [subrangeType(tau1), tau1]: return tau1;
           //case [subrangeType(tau1), subrangeType(tau1)]: return tau1;
           case [setType(tau1), setType(tau1)]: return setType(tau1);
           default:
                s.report(error(e, "%q not defined on %t and %t", op, exp1, exp2));  
       }
     });
     collect(exp1, exp2, c);
}

void collect(e: (Expression) `<Expression exp1> + <Expression exp2>`, Collector c)
    = overloadAdding(e, "+", exp1, exp2, c);

void collect(e: (Expression) `<Expression exp1> - <Expression exp2>`, Collector c)
    = overloadAdding(e, "-", exp1, exp2, c);

void collect(e: (Expression) `<Expression exp1> or <Expression exp2>`, Collector c){
    c.calculate("or", e, [exp1, exp2], 
        AType(Solver s) { switch([s.getType(exp1), s.getType(exp2)]){
                      case [booleanType(), booleanType()]: return booleanType();
                      default:      
                            s.report(error(e, "%q not defined on %t and %t", "or", exp1, exp2));
                  }
                });  
     collect(exp1, exp2, c);
}

// Variable

void collect(current: (FieldDesignator) `<RecordVariable var> . <FieldIdentifier field>`, Collector c){
    c.useViaType(var, field, {fieldId()});
    c.fact(current, field);
    collect(var, field, c);
}

void collect(current: (IndexedVariable) `<ArrayVariable var> [ <{Expression ","}+ indices> ]`, Collector c){
     c.calculate("indexed variable", current, var + [exp | Expression exp <- indices],
        AType (Solver s){ 
            if(arrayType(tau1, tau2) := s.getType(var)){
               indexType = atypeList([s.getType(exp) | exp <- indices]);
               s.requireSubType(indexType, tau1, error(current, "Index mismatch, expected %t, found %t", tau1, indexType));
                return tau2;
              } else {
                s.report(error(current, "Array type required, found %t", var));
              }
           });
     collect(var, indices, c);
}

void collect(fd: (FunctionDesignator)  `<FunctionIdentifier fid> ( <{ ActualParameter ","}+  actuals> )`, Collector c){
     c.use(fid, {functionId()});
     actualList = [exp | Tree exp <- actuals];
     
     // int -> int; real -> real
     AType iirr(Solver s) { switch(s.getType(actualList[0])){
                        case integerType(): return integerType();
                        case realType(): return realType();
                        default:
                            s.report(error(fd, "Illegal call of %q with argument %t", fid, actualList[0]));
                      }
                      return realType();
                    };
     // int -> real; real -> real              
      ;
     switch("<fid>"){
     
     case "abs": 
        c.calculate("call `abs`", fd, actualList, iirr);  
     case "arctan": 
        c.calculate("call `arctan`", fd, actualList, iirr);
     case "cos": 
        c.calculate("call `cos`", fd, actualList, iirr);
     case "exp": 
        c.calculate("call `exp`", fd, actualList, iirr);
     case "ln": 
        c.calculate("call `ln`", fd, actualList, iirr);
     case "sin": 
        c.calculate("call `sin`", fd, actualList, iirr);
     case "sqr": 
        c.calculate("call `sqr`", fd, actualList, iirr);
     case "sqrt": 
        c.calculate("call `sqrt`", fd, actualList, iirr);
 
     default: {
        Tree tfid = fid;
        c.calculate("function designator", fd, [tfid] + [exp | Tree exp <- actuals],
            AType(Solver s) { 
                if(functionType(tau1, tau2) := s.getType(fid)){ 
                    actualParamType = atypeList([s.getType(exp) | exp <- actuals]);
                    s.requireSubType(actualParamType, tau1, error(fd, "Parameter mismatch, expected %t, found %t", tau1, actualParamType));
                    return tau2;
                } else {
                    s.report(error(fd, "Function type required, found %t", fid));
                }
            });
        }
      }
      
      collect(actuals, c);
}

// set

void collect(current: (Set) `[ <{Element ","}* elements> ]`, Collector c){
     c.calculate("set", current, [exp | exp <- elements],
            AType(Solver s) { 
                elemTypes = {subrangeType(assocType) := tp ? assocType : tp | exp <- elements, tp := s.getType(exp)};
                if(size(elemTypes) == 0) return setType(voidType());
                if(size(elemTypes) > 1) s.report(error(current, "Elements of set should have the same type, found %t", elemTypes));
                elemType = getFirstFrom(elemTypes);
                s.requireTrue(isScalarType(elemType), error(current, "Elements of set should be a scalar type, found %t", elemType));
                return setType(elemType);
            });
      collect(elements, c);
}

void collect(current: (Element) `<Expression from> .. <Expression to>`, Collector c){
    c.requireEqual(from, to, error(current, "Set element range requires lower and upper bound of equal type, found %t and %t", from, to));
    c.calculate("set element range", current, [from, to],
        AType(Solver s) { return subrangeType(s.getType(from)); });
    collect(from, to, c);

}

void collect(s: (ProcedureStatement)  `<ProcedureIdentifier fid>`, Collector c){
     c.use(fid, {procedureId(), functionId()});
}

void collect(current: (ProcedureStatement) `<ProcedureIdentifier id> ( <{ActualParameter ","}+ actuals> )`, Collector c){
     c.use(id, {procedureId(), functionId()});
     actualList = [exp | exp <- actuals];
         
     switch("<id>"){
     case "new": {
            if(size(actualList) != 1){
                c.report(error(current, "One argument required"));
            }
            c.require("new", current, actualList,
                void(Solver s){
                    s.requireTrue(pointerType(t) := s.getType(actuals[0]), error(current, "pointer type required, found %t", actuals[0]));
                });
        }
     case "read":;
     case "write":;
     case "writeln":;
     
     default: {
        Tree tid = id;
        c.require("procedure statement", current, [tid] + [exp | Tree exp <- actuals],
           void(Solver s) { 
                if(procedureType(tau1) := s.getType(id)){ 
                    actualType = atypeList([s.getType(exp) | exp <- actuals]);
                    s.requireSubType(actualType, tau1, error(current, "Parame, expected %t, found %t", tau1, actualType));
                  } else {
                    s.report(error(current, "Procedure type required, found", id));
                  }
               });
         }
     }
     
     collect(actuals, c);
}

// goto statement

void collect(GoToStatement s, Collector c){
     c.use(s.label, {labelId()});
}

void collect(current: (Expression) `( <Expression exp> )`, Collector c){
    c.fact(current, exp);
}

// compound statement

void collect(current: (CompoundStatement) `begin <{ Statement ";" }+ statements> end`, Collector c){
    collect(statements, c);
}

// conditional statement

void collect(current: (IfStatement) `if <Expression condition> then <Statement thenStat>`, Collector c){
    c.requireEqual(condition, booleanType(), error(condition, "Condition should be `boolean`, found %t", condition));
    collect(condition, thenStat, c);
}

void collect(current: (IfStatement) `if <Expression condition> then <Statement thenStat> else <Statement elseStat>`, Collector c){
    c.requireEqual(condition, booleanType(), error(condition, "Condition should be `boolean`, found %t", condition));
    collect(condition, thenStat, elseStat, c);
}

// Case statement

void collect(current: (CaseStatement) `case <Expression exp> of <{CaseListElement ";"}+ caseElements>  end`, Collector c){
    caseLabelList = [clab | (CaseListElement) `<{ CaseLabel ","}+ caseLabels> : <Statement caseStatement>` <- caseElements,"<caseLabels>" != "", clab <- caseLabels];

    c.require("case statement", current, exp + caseLabelList,
        void(Solver s){
            expType = s.getType(exp);
            for(clab <- caseLabelList){
                s.requireSubType(clab, expType, error(clab, "Case label %q should be compatible with selector type %t, found %t","<clab>", expType, clab));
            }
        });
    collect(exp, caseElements, c);
}

void collect(current : (CaseListElement) `<CaseLabelList caseLabels> : <Statement caseStatement>`, Collector c){
    collect(caseLabels, caseStatement, c);
}

// while statement

void collect(current: (WhileStatement) `while <Expression condition> do <Statement doStat>`, Collector c){
    c.requireEqual(condition, booleanType(), error(condition, "Condition should be `boolean`, found %t", condition));
    collect(condition, doStat, c);
} 

// repeat statement

void collect(current: (RepeatStatement) `repeat <{Statement ";"}+ repeatStats> until <Expression condition>`, Collector c){
   c.requireEqual(condition, booleanType(), error(condition, "Condition should be `boolean`, found %t", condition));
   collect(repeatStats, condition, c);
}

// for statement

void collect(current: (ForStatement) `for <Identifier control> := <ForList forList> do <Statement doStat>`, Collector c){
    c.enterScope(current);
        c.define("<control>", variableId(), control, defType(integerType()));
        collect(forList, doStat, c);
    c.leaveScope(current);
}

void collect(current:(ForList) `<Expression initial> to <Expression final>`, Collector c){
    c.require("for list to", current, [initial, final],
        void(Solver s){
            initialType = s.getType(initial);
            finalType = s.getType(final);
            s.requireTrue(isScalarType(initialType), error(initial, "Initial value should be scalar type, found %t", initialType));
            s.requireEqual(initialType, finalType, error(initial, "Initial and final value should have the same type, found %t and %t", initialType, finalType));
         });
    collect(initial, final, c);
}

void collect(current:(ForList) `<Expression initial> downto <Expression final>`, Collector c){
     c.require("for list downto", current, [initial, final],
        void(Solver s){
            initialType = s.getType(initial);
            finalType = s.getType(final);
            s.requireTrue(isScalarType(initialType), error(initial, "Initial value should be scalar type, found %t", initialType));
            s.requireEqual(initialType, finalType, error(initial, "Initial and final value should have the same type, found %t and %t", initialType, finalType));
         });
    collect(initial, final, c);
}

// with statement

void collect(current: (WithStatement) `with <{RecordVariable ","}+ recordVars> do <Statement withStat>`, Collector c){
    c.enterScope(current);
        for(rv <- recordVars){
            c.addPathToType(rv, withPath());
        }
        collect(recordVars, withStat, c);
    c.leaveScope(current);
}
