module analysis::typepal::Utils

import List;
import ParseTree;

loc getFirstLoc(Tree t) {
    for (a <- t.args) {
        if (a@\loc?) {
            return a@\loc;
        }
    }
    throw "Cannot find loc on tree";
}

loc getLastLoc(Tree t) {
    for (i <- [size(t.args)-1..-1]) {
        if (t.args[i]@\loc?) {
            return  t.args[i]@\loc;
        }
    }
    throw "Cannot find loc on tree";
}

loc getLoc(Tree t)
    = t@\loc ? { fst = getFirstLoc(t); 
                 lst = getLastLoc(t);
                 n = fst[length=lst.offset - fst.offset + lst.length]; 
                 (n.end? && lst.end?) ? n[end=lst.end] : n;
                 };