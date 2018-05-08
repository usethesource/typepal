@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::TypePal
       
import Set; 
import Node;
import Map;
import IO;
import List; 
import ParseTree;
import String;
import Message;
import Exception;

extend analysis::typepal::AType;
extend analysis::typepal::Collector;
extend analysis::typepal::FailMessage;
extend analysis::typepal::Messenger;
extend analysis::typepal::ScopeGraph;
extend analysis::typepal::Solver;
import analysis::typepal::TestFramework;
extend analysis::typepal::TypePalConfig;
extend analysis::typepal::Utils;

// collectAndSolve shorthand for a common, simple, scenario

TModel collectAndSolve(Tree pt, TypePalConfig config = tconfig(), bool debug = false){
    if(pt has top) pt = pt.top;
    c = newCollector("Pico", pt, config=config, debug=debug);
    collect(pt, c);
    return newSolver(pt, c.run(), debug=debug).run();
}

// Utilities on TModels that can help to build IDE-features


rel[loc, loc] getUseDef(TModel tm){
    res = {};
    for(Use u <- tm.uses + tm.indirectUses){
        try {
           foundDefs =  lookup(tm, u);
           res += { <u.occ, def> | def <- foundDefs };
        } catch NoBinding(): {
            ;// ignore it
        } catch AmbiguousDefinition(_):{
            ;// ignore it
        }
    };
    return res;
}

set[str] getVocabulary(TModel tm)
    = {d.id | Define d <- tm.defines};

map[loc, AType] getFacts(TModel tm)
    = tm.facts;

list[Message] getMessages(TModel tm)
    = tm.messages;
