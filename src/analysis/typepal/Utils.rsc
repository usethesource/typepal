module analysis::typepal::Utils

import ParseTree;

loc getLoc(Tree t)
    = t@\loc ? { fst = t.args[0]@\loc; 
                 lst = t.args[-1]@\loc;
                 n = fst[length=lst.offset - fst.offset + lst.length]; 
                 (n.end? && lst.end?) ? n[end=lst.end] : n;
                 };

                 