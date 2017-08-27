module typepal::TestFramework

import ParseTree;
import IO;
import String;
import Set;
import Map;
import List;

extend typepal::TypePal;
import analysis::grammars::Ambiguity;

//import util::IDE;
import util::Reflective;

lexical TTL_id = ([A-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ TTL_Reserved;
lexical TTL_String = "\"" ![\"]*  "\"";

keyword TTL_Reserved = "test" | "expect" ;

layout TTL_Layout = TTL_WhitespaceAndComment* !>> [\ \t\n\r];

lexical TTL_WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "@@" ![\n]+
   | @category="Comment" ws3: "\<@@" ![]*  "@@\>"
   ;
   
start syntax TTL = ttl: TTL_TestItem* items ;

lexical TTL_Token = ![\[\]] | "[" ![\[]* "]";

syntax TTL_TestItem
    = "test" TTL_id name "[[" TTL_Token* tokens "]]" TTL_Expect expect
    ;

syntax TTL_Expect
    = none: ()
    | "expect" "{" {TTL_String ","}* messages "}"
    ;
    
bool matches(str subject, str pat) =
    contains(toLowerCase(subject), toLowerCase(pat));

FRBuilder emptyFRBuilder(Tree t) = newFRBuilder();

str deescape(str s)  {  // copied from RascalExpression, belongs in library
    res = visit(s) { 
        case /^\\<c: [\" \' \< \> \\]>/ => c
        case /^\\t/ => "\t"
        case /^\\n/ => "\n"
        case /^\\u<hex:[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]>/ => stringChar(toInt("0x<hex>"))
        case /^\\U<hex:[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]>/ => stringChar(toInt("0x<hex>"))
        case /^\\a<hex:[0-7][0-9a-fA-F]>/ => stringChar(toInt("0x<hex>"))
        }; 
    return res;
}

bool runTests(loc tests, type[&T<:Tree] begin, FRBuilder(Tree) initialFRBuilder = emptyFRBuilder,
                      bool(AType atype1, AType atype2, FRModel frm) isSubType = noIsSubType,
                      AType(AType atype1, AType atype2, FRModel frm) getLUB = noGetLUB,
                      bool verbose = false
){
    TTL ttlProgram;
    
    tr = parse(#start[TTL], tests, allowAmbiguity=true);

    // TODO: layout of the subject language may interfere with laout of TTL
   //       but this is a too harsh measure!
   
    if(amb(set[Tree] alternatives) := tr){
        ttlProgram = visit(tr){ case amb(set[Tree] alternatives1) => getOneFrom(alternatives1) }.top;
    } else {
        ttlProgram = visit(tr.top){ case amb(set[Tree] alternatives2) => getOneFrom(alternatives2) };
    }

    ok = true;
    failedTests = ();
    ntests = 0;
    for(ti <- ttlProgram.items){
        ntests += 1;
        try {
           p = parse(begin, "<ti.tokens>");
          <messages, model> = validate(enhanceFRModel(extractFRModel(p, initialFRBuilder(p))), isSubType=isSubType, getLUB=getLUB);
          if(verbose) println("runTests: <messages>");
          ok = ok && isEmpty(messages);
          expected = ti.expect is none ? {} : {deescape("<s>"[1..-1]) | TTL_String s <- ti.expect.messages};
          result = (isEmpty(messages) && isEmpty(expected)) || all(emsg <- expected, any(eitem <- messages, matches(eitem.msg, emsg)));
          println("Test <ti.name>: <result>");
          if(!result) failedTests["<ti.name>"] = relocate(messages, ti.tokens@\loc); 
          //if(!result) iprintln(relocate(model, ti.tokens@\loc));  
       } catch ParseError(loc l): {
            failedTests["<ti.name>"]  = {error("Parse error", relocate(l, ti.tokens@\loc))};
       } 
    }
    nfailed = size(failedTests);
    println("Test summary: <ntests> tests executed, <ntests - nfailed> succeeded, <nfailed> failed");
    if(!isEmpty(failedTests)){
        println("Failed tests:");
        for(failed <- failedTests){
            println("<failed>:");
            for(msg <- failedTests[failed]){
                println("\t<msg>");
            }
        }
    }
    return ok;
}

loc relocate(loc osrc, loc base){
    nsrc = base;
    
    nsrc.offset = base.offset + osrc.offset;
    nsrc.length = osrc.length;
    
    nsrc.end.line = base.begin.line + osrc.end.line - 1;
    nsrc.begin.line = base.begin.line + osrc.begin.line - 1;
    
    if(osrc.end.line == 1){
        nsrc.end.column = base.begin.column + osrc.end.column;
    } else {
        nsrc.end.column = osrc.end.column;
    }
    
    if(osrc.begin.line == 1){
        nsrc.begin.column = base.begin.column + osrc.begin.column;
    } else {
        nsrc.begin.column = osrc.begin.column;
    }
    
    //println("relocate with base <base>: from <osrc> to <nsrc>");
    return nsrc;
}

Message relocate(Message msg, loc base){
    msg.at = relocate(msg.at, base);
    return msg;
}

set[Message] relocate(set[Message] messages, loc base)
    = { relocate(msg, base) | msg <- messages };

FRModel relocate(FRModel frm, loc base){
    return visit(frm) {
           case loc l => relocate(l, base) when l.scheme == "unknown"
    }

}
//void register() {
//    registerLanguage("TTL", "ttl", Tree (str x, loc l) { return parse(#start[TTL], x, l, allowAmbiguity=true); });
//    registerContributions("TTL", {
//      syntaxProperties(
//         fences = {<"{","}">,<"[[","]]">} ,
//         lineComment = "@@",
//         blockComment = <"\<@@"," *","@@\>">
//         )
//    });
//}    