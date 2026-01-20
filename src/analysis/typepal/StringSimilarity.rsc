@license{
Copyright (c) 2024, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
module analysis::typepal::StringSimilarity

import Location;
import Set;
import String;
import analysis::typepal::TModel;
import analysis::typepal::ConfigurableScopeGraph;

@synopsis{Tryadic minimum function on integers}
int min(int a, int b, int c)
=   a < b ? (a < c ? a : c) : (b < c ? b : c);

@synopsis{Calculate the Levenshtein distance of 2 strings}
int lev(str a, str b){
    int sizea = size(a);
    int sizeb = size(b);

    @memo{expireAfter(minutes=1),maximumSize(50)}
    int lev(int ia, int ib){
        if(ib == sizeb) return sizea - ia;
        if(ia == sizea) return sizeb - ib;
        if(a[ia] == b[ib]) return lev(ia+1, ib+1);

        return 1 + min(lev(ia+1, ib),
                       lev(ia,   ib+1),
                       lev(ia+1, ib+1));
    }

    return  lev(0, 0);
}

// Tests for `lev`

test bool levCommutative(str a, str b) = lev(a, b) == lev(b, a);

test bool levLeftAdditive(str a, str b, str c) = lev(a, b) == lev(c + a, c + b);

test bool lev1() = lev("kitten", "sitting") == 3;
test bool lev2() = lev("kelm", "hello") == 3;
test bool lev3() = lev("hello", "hella") == 1;
test bool lev4() = lev("hello", "") == 5;
test bool lev5() = lev("", "hello") == 5;
test bool lev6() = lev("aap", "noot") == 4;
test bool lev7() = lev("page", "pope") == 2;
test bool lev8() = lev("december", "january") == 8;
test bool lev9() = lev("march", "may") == 3;

// Similarity functions to be used by TypePal

@synopsis{WordSim represents one word from the vocabulary and its similariy to the original word}
alias WordSim = tuple[str word, int sim];

@synopsis{Compute list of words from vocabulary, that are similar to give word w with at most maxDistance edits}
list[str] similarWords(str w, set[str] vocabulary, int maxDistance)
= sort({ <v, d> | str v <- vocabulary, d := lev(w, v), d <= maxDistance }, 
                  bool (WordSim x, WordSim y){ return x.sim < y.sim;}).word;

// TODO: remove this temporary copy of isContainedIn (needed to break deployment cycle)
// should reside in Location.rsc
private bool isContainedIn(loc inner, loc outer, map[loc,loc] m)
    = isContainedIn(inner in m ? m[inner] : inner, outer in m ? m[outer] : outer);

@synopsis{Find in TModel tm, names similar to Use u. Max edit distance comes from TypePal Configuration.}
list[str] similarNames(Use u, TModel tm){
    w = getOrgId(u);
    idRoles = u.idRoles;
    vocabulary = { d.orgId | d <- tm.defines, d.idRole in idRoles, isContainedIn(u.occ, d.scope, tm.logical2physical) };
    return similarWords(w, vocabulary, tm.config.cutoffForNameSimilarity);
}
