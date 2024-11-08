module analysis::typepal::StringSimilarity

import String;
import List;

int min(int a, int b, int c)
=   a < b ? (a < c ? a : c) : (b < c ? b : c);

@synopsis{Calculate the Levenshtein distance of 2 strings}
@memo
int lev(str a, str b)
    = lev(a, 0, b, 0);

@memo
private int lev(str a, int ia, str b, int ib){
    if(ib == size(b)) return size(a) - ia;
    if(ia == size(a)) return size(b) - ib;
    if(a[ia] == b[ib]) return lev(a, ia+1, b, ib+1);

    return 1 + min(lev(a, ia+1, b, ib),
                   lev(a, ia,   b, ib+1),
                   lev(a, ia+1, b, ib+1));
}

// @memo
// private int lev(str a, int ia, int lena, str b, int ib, int lenb){
//     if(lenb == 0) return lena;
//     if(lena == 0) return lenb;
//     if(a[ia] == b[ib]) return lev(a, ia+1, lena-1, b, ib+1, lenb-1);

//     return 1 + min(lev(a, ia+1, lena-1, b, ib,   lenb),
//                    lev(a, ia,   lena,   b, ib+1, lenb-1),
//                    lev(a, ia+1, lena-1, b, ib+1, lenb-1));
// }

test bool lev0(str a, str b) = lev(a, b) == lev(b, a);

test bool levx(str a, str b, str c) = lev(a, b) == lev(c + a, c + b);

test bool lev1() = lev("kitten", "sitting") == 3;
test bool lev2() = lev("kelm", "hello") == 3;
test bool lev3() = lev("hello", "hella") == 1;
test bool lev4() = lev("hello", "") == 5;
test bool lev5() = lev("", "hello") == 5;
test bool lev6() = lev("aap", "noot") == 4;
test bool lev7() = lev("page", "pope") == 2;
test bool lev8() = lev("december", "january") == 8;
test bool lev9() = lev("march", "may") == 3;


alias WordSim = tuple[str word, int sim];

list[str] similarWords(str w, list[str] vocabulary, int maxDistance)
= sort([ <v, d> | str v <- vocabulary, d := lev(w, v), d <= maxDistance ], bool (WordSim x, WordSim y){ return x.sim < y.sim;}).word;

value main() = similarWords("ac", ["a", "ab", "ac", "x"], 10);