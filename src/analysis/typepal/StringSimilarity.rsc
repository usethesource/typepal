module analysis::typepal::StringSimilarity

import List;
import IO;
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

@synopsis{Find in TModel tm, names similar to Use u. Max edit distance comes from TypePal Configuration.}
list[str] similarNames(Use u, TModel tm){
    w = getOrgId(u);
    idRoles = u.idRoles;
    vocabulary = { d.orgId | d <- tm.defines, d.idRole in idRoles, isContainedIn(u.occ, d.scope) };
    return similarWords(w, vocabulary, tm.config.cutoffForNameSimilarity);
}
