module TestFramework

import ParseTree;
import IO;
import String;
import Set;
import Map;
import List;
import Constraints;

lexical Id = ([A-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ Reserved;
lexical Natural = [0-9]+ ;
lexical String = "\"" ![\"]*  "\"";

keyword Reserved = "test" | "expect" ;

layout Layout = WhitespaceAndComment* !>> [\ \t\n\r%];

lexical WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2:
    "%" ![%]+ "%"
   | @category="Comment" ws3: "{" ![\n}]*  "}"$
   ;
   
start syntax TTL = ttl: TestItem* items;

lexical Token = ![\[\]] | "[" ![\[]* "]";

start syntax TestItem
    = "test" Id name "[[" Token* tokens "]]" Expect expect
    ;

syntax Expect
    = none: ()
    | "expect" "{" {String ","}* messages "}"
    ;
    
bool matches(str subject, str pat) =
    contains(toLowerCase(subject), toLowerCase(pat));

SGBuilder emptySGBuilder(Tree t) = scopeGraphBuilder();

bool runTests(loc tests, type[&T<:Tree] begin, SGBuilder(Tree) initialSGBuilder = emptySGBuilder,
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
        messages = validate(extractScopesAndConstraints(p, initialSGBuilder(p)), isSubtype=isSubtype, getLUB=getLUB);
        println("runTests: <messages>");
        ok = ok && isEmpty(messages);
        expected = ti.expect is none ? {} : {"<s>"[1..-1] | String s <- ti.expect.messages};
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