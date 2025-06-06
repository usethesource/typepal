@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::GetLoc

/*
    Convenience functions to get the location of a Tree
*/
import List;
import ParseTree;
import IO;

loc getFirstLoc(Tree t) {
    for (a <- t.args) {
        if (a@\loc?) {
            return a@\loc;
        }
    }
    if(t@\loc?){
        return t@\loc;
    }
    println("PANIC: getFirstLoc");
    println("Source text: <t>");
    println("ParseTree: "); iprintln(t, lineLimit=10000);
    throw "Cannot find loc on tree";
}

loc getLastLoc(Tree t) {
    for (i <- [size(t.args)-1..-1]) {
        if (t.args[i]@\loc?) {
            return  t.args[i]@\loc;
        }
    }
    if(t@\loc?){
        return t@\loc;
    }
    throw "Cannot find loc on tree";
}

loc getLoc(Tree t)
    = t@\loc ? { fst = getFirstLoc(t); 
                 lst = getLastLoc(t);
                 n = fst[length=lst.offset - fst.offset + lst.length]; 
                 (n.end? && lst.end?) ? n[end=lst.end] : n;
                 };