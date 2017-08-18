module typepal::TestFramework

import ParseTree;
import IO;
import String;
import Set;
import Map;
import List;

extend typepal::TypePal;

import util::IDE;

lexical TTL_id = ([A-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ TTL_Reserved;
lexical TTL_Natural = [0-9]+ ;
lexical TTL_String = "\"" ![\"]*  "\"";

keyword TTL_Reserved = "test" | "expect" ;

layout TTL_Layout = TTL_WhitespaceAndComment* !>> [\ \t\n\r];

lexical TTL_WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "@@" ![\n]+
   | @category="Comment" ws3: "\<@@" ![]*  "@@\>"
   ;
   
start syntax TTL = ttl: TTL_TestItem* items;

lexical TTL_Token = ![\[\]] | "[" ![\[]* "]";

start syntax TTL_TestItem
    = "test" TTL_id name "[[" TTL_Token* tokens "]]" TTL_Expect expect
    ;

syntax TTL_Expect
    = none: ()
    | "expect" "{" {TTL_String ","}* messages "}"
    ;
    
bool matches(str subject, str pat) =
    contains(toLowerCase(subject), toLowerCase(pat));

FRBuilder emptyFRBuilder(Tree t) = makeFRBuilder();

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
                      bool(AType atype1, AType atype2, ScopeGraph sg) isSubtype = noIsSubtype,
                      AType(AType atype, ScopeGraph sg) getLUB = noGetLUB,
                      bool verbose = false
){
    ttlProgram = parse(#start[TTL], tests).top;
    ok = true;
    failedTests = ();
    ntests = 0;
    for(ti <- ttlProgram.items){
        ntests += 1;
        p = parse(begin, "<ti.tokens>");
        <messages, model> = validate(extractScopesAndConstraints(p, initialFRBuilder(p)), isSubtype=isSubtype, getLUB=getLUB);
        if(verbose) println("runTests: <messages>");
        ok = ok && isEmpty(messages);
        expected = ti.expect is none ? {} : {deescape("<s>"[1..-1]) | TTL_String s <- ti.expect.messages};
        result = (isEmpty(messages) && isEmpty(expected)) || all(emsg <- expected, any(eitem <- messages, matches(eitem.msg, emsg)));
        println("Test <ti.name>: <result>");
        if(!result) failedTests["<ti.name>"] = messages;     
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


void register() {
    registerLanguage("TTL", "ttl", Tree (str x, loc l) { return parse(#start[TTL], x, l, allowAmbiguity=true); });
    registerContributions("TTL", {
      syntaxProperties(
         fences = {<"{","}">,<"[[","]]">} ,
         lineComment = "@@",
         blockComment = <"\<@@"," *","@@\>">
         )
    });
}    