module TestFramework

import ParseTree;
import IO;
import String;
import Set;
import Map;
import List;
import Constraints;

lexical TTL_id = ([A-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ TTL_Reserved;
lexical TTL_Natural = [0-9]+ ;
lexical TTL_String = "\"" ![\"]*  "\"";

keyword TTL_Reserved = "test" | "expect" ;

layout TTL_Layout = TTL_WhitespaceAndComment* !>> [\ \t\n\r%];

lexical TTL_WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   //| @category="Comment" ws3: "{" ![\n}]*  "}"$
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

bool runTests(loc tests, type[&T<:Tree] begin, FRBuilder(Tree) initialFRBuilder = emptyFRBuilder,
                      bool(AType atype1, AType atype2, ScopeGraph sg) isSubtype = noIsSubtype,
                      AType(AType atype, ScopeGraph sg) getLUB = noGetLUB
){
    ttlProgram = parse(#TTL, tests);
    ok = true;
    failed = ();
    ntests = 0;
    for(ti <- ttlProgram.items){
        ntests += 1;
        p = parse(begin, "<ti.tokens>");
        <messages, model> = validate(extractScopesAndConstraints(p, initialFRBuilder(p)), isSubtype=isSubtype, getLUB=getLUB);
        println("runTests: <messages>");
        ok = ok && isEmpty(messages);
        expected = ti.expect is none ? {} : {"<s>"[1..-1] | TTL_String s <- ti.expect.messages};
        result = (isEmpty(messages) && isEmpty(expected)) || all(emsg <- expected, any(eitem <- messages, matches(eitem.msg, emsg)));
        println("Test <ti.name>: <result>");
        if(!result) failed["<ti.name>"] = result;     
    }
    nfailed = size(failed);
    println("Test summary: <ntests> tests executed, <ntests - nfailed> succeeded, <nfailed> failed");
    if(!isEmpty(failed)){
        println("Failed tests:");
        iprintln(failed);
    }
    return ok;
}