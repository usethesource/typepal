@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::TestFramework

import ParseTree;
import IO;
import String;
import Set;
import Map;
import List;
import util::Benchmark;

extend analysis::typepal::Messenger;
extend analysis::typepal::TypePal;

lexical TTL_id = ([A-Z][a-zA-Z0-9]* !>> [a-zA-Z0-9]) \ TTL_Reserved;
lexical TTL_StringCharacter
    = "\\" [\" \' \< \> \\ b f n r t]  
    | ![\" \' \< \> \\]
    | [\n][\ \t \u00A0 \u1680 \u2000-\u200A \u202F \u205F \u3000]* [\'] // margin 
    ;

lexical TTL_String = "\"" TTL_StringCharacter*  "\"";

keyword TTL_Reserved = "test" | "expect" ;

layout TTL_Layout = TTL_WhitespaceAndComment* !>> [\ \t\n\r];

lexical TTL_WhitespaceAndComment 
   = [\ \t\n\r]
   | @category="Comment" ws2: "@@" ![\n]+ $
   | @category="Comment" ws3: "\<@@" (![@] | "@" !>> "@" | "@@" !>> [\>])*  "@@\>"
   ;
   
start syntax TTL = ttl: TTL_TestItem* items ;

lexical TTL_Token 
    = ![\]] 
    | "]" !<< "]" !>> "]"
    ;

syntax TTL_TestItem
    = "test" TTL_id name "[[" TTL_Token* tokens "]]" TTL_Expect expect
    ;

syntax TTL_Expect
    = none: ()
    | "expect" "{" {TTL_String ","}* messages "}"
    ;

data Tree(loc src = |unknown:///|);

bool matches(str subject, str pat){
    pat = uncapitalize(pat);
    subject = uncapitalize(subject);
    return all(p <- split("_", pat), contains(subject, p));
}

str spinChar(int n)
    = n < 0 ? "|" : (0: "|", 1: "/", 2: "-", 3: "\\")[n%4];

bool runTests(list[loc] suites, type[&T<:Tree] begin, TModel(Tree t) getModel, bool verbose = false, set[str] runOnly = {}, str runName = ""){
    TTL ttlProgram = [TTL] "";
    
    map[tuple[str, loc], list[Message]]failedTests = ();
    int ntests = 0;
    bool ok = true;
    int parseTime = 0;
    int testTime = 0;
    if(runName?) print("Running <runName> Tests\r");
    for(suite <- suites){
        startParse = cpuTime(); 
        tr = parse(#start[TTL], suite, allowAmbiguity=true);
        parseTime += (cpuTime() - startParse);
    
        // TODO: layout of the subject language may interfere with layout of TTL but this is a too harsh measure!
       
        if(amb(set[Tree] _) := tr){
            ttlProgram = visit(tr){ case amb(set[Tree] alternatives1) => getOneFrom(alternatives1) }.top;
        } else {
            ttlProgram = visit(tr.top){ case amb(set[Tree] alternatives2) => getOneFrom(alternatives2) };
        }
        startTests = cpuTime(); 
        for(TTL_TestItem ti <- ttlProgram.items){
            if (runOnly != {} && "<ti.name>" notin runOnly) {
                continue;
            }
            ntests += 1;
            try {
              newTree = visit(parse(begin, "<ti.tokens>")) {
                case Tree t => t[src = relocate(t.src, ti.tokens.src)]
                    when t has src
              };
              model = getModel(newTree);
              list[Message] messages = model.messages;
              if(verbose) println("runTests: <messages>");
              expected = ti.expect is none ? {} : {deescape("<s>"[1..-1]) | TTL_String s <- ti.expect.messages};
              result = (isEmpty(messages) && isEmpty(expected)) || any(emsg <- expected, any(eitem <- messages, matches(eitem.msg, emsg)));
              ok = ok && result;
              print("<spinChar(ntests)> Test <ti.name>: <result>          \r");
              if(!result) failedTests[<"<ti.name>", suite>] = messages; 
              //if(!result) iprintln(model);  
           } catch ParseError(loc l): {
                failedTests[<"<ti.name>", suite>]  = [error("Parse error", relocate(l, ti.tokens@\loc))];
           } catch Ambiguity(loc l, nt, inp): {
                failedTests[<"<ti.name>", suite>]  = [error("Ambiguity (<nt> on `<inp>`)", (l.offset?) ? relocate(l, ti.tokens@\loc) : l)];
           } 

        }
        testTime += (cpuTime() - startTests);
    }
    nfailed = size(failedTests);
    heading = (runName? ? (runName + " ") : "") + "Test Summary";
    println("<heading>: <ntests> tests executed, <ntests - nfailed> succeeded, <nfailed> <nfailed == 0 ? "failed" : "FAILED">");
    if(!isEmpty(failedTests)){
        println("Failed tests:");
        for(failed <- failedTests){
            msgs = failedTests[failed];
            <name, suite> = failed;
           
            if(isEmpty(msgs)){
                println("<suite>, <name>:\tExpected message not found");
            } else {
                println("<suite>, <name>:");
                for(msg <- sortMostPrecise(msgs)){
                    println("\t<msg>");
                }
            }
        }
    }
    println("Parse time: <parseTime/1000000> msec; Test time: <testTime/1000000> msec");
    return ok;
}

lrel[&T<:Tree, set[str]] extractTests(list[loc] suites, type[&T<:Tree] begin) {
    result = [];
    for(suite <- suites){
        tr = parse(#start[TTL], suite, allowAmbiguity=true);
        TTL ttlProgram = [TTL] "";
        if(amb(set[Tree] _) := tr){
            ttlProgram = visit(tr){ case amb(set[Tree] alternatives1) => getOneFrom(alternatives1) }.top;
        } else {
            ttlProgram = visit(tr.top){ case amb(set[Tree] alternatives2) => getOneFrom(alternatives2) };
        }
        
        for(TTL_TestItem ti <- ttlProgram.items){
            t = parse(begin, "<ti.tokens>");
            result += <relocate(t, ti.tokens@\loc), ti.expect is none ? {} : {deescape("<s>"[1..-1]) | TTL_String s <- ti.expect.messages}>;
        }
    }
    return result;
}

&T<:Tree relocate(&T<:Tree t, loc container) {
    return visit (t) {
        case Tree tt => tt[@\loc = relocate(tt@\loc, container)]
            when tt has \loc
    };
}

loc relocate(loc parsed_in_container, loc container){
    res = parsed_in_container;
    if(parsed_in_container.offset?){
        offset = container.offset + parsed_in_container.offset;
        length = parsed_in_container.length;
        
        endline = container.begin.line + parsed_in_container.end.line - 1;
        beginline = container.begin.line + parsed_in_container.begin.line - 1;
        
        begincolumn = parsed_in_container.begin.line == 1 
                      ? container.begin.column + parsed_in_container.begin.column
                      : parsed_in_container.begin.column;
       
        endcolumn = parsed_in_container.end.line == 1 
                    ? container.begin.column + parsed_in_container.end.column
                    : parsed_in_container.end.column;
        
        res = |<container.scheme>://<container.authority>/<container.path>|(offset, length, <beginline, begincolumn>, <endline, endcolumn>);
    }
    return res;
}

//loc relocate(loc parsed_in_container, loc container) = (container.top)[offset = container.offset + parsed_in_container.offset][length = parsed_in_container.length];

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
