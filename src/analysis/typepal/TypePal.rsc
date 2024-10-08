@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::TypePal

/*
    Top level module that provides all TypePal functionality to its clients
    and also declares some convenience functions.
*/
          
import ParseTree;
import Message;

extend analysis::typepal::Solver;
extend analysis::typepal::Version;

// collectAndSolve shorthand for a common, simple, scenario

TModel collectAndSolve(Tree pt, TypePalConfig config = tconfig(), str modelName = "no-name"){
    if(pt has top) pt = pt.top;
    c = newCollector(modelName, pt, config);
    collect(pt, c);
    return newSolver(pt, c.run()).run();
}

// Utilities on TModels that can help to build IDE-features

rel[loc, loc] getUseDef(TModel tm)
    = tm.useDef;

set[str] getVocabulary(TModel tm)
    = {d.id | Define d <- tm.defines};

map[loc, AType] getFacts(TModel tm)
    = tm.facts;

list[Message] getMessages(TModel tm)
    = tm.messages;
