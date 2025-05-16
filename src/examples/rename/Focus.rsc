module examples::rename::Focus

import IO;

import Location;
import String;
import ParseTree;

bool isContainedIn(Tree tr, int line, int col) {
    if (!tr.src?) return false;
    tuple[int line, int col] begin = tr.src.begin;
    tuple[int line, int col]  end = tr.src.end;

    if (line < begin.line) return false;
    if (line > end.line) return false;
    if (line == begin.line) {
        if (col < begin.col) return false;
        if (line == end.line) return col <= end.col; // single line
        return line <= end.line; // cursor on first line of tree
    }
    // line > begin.line && line < end.line
    if (line == end.line) return col <= end.col; // cursor on last line of tree
    return true;
}

public list[Tree] computeFocusList(Tree tr, int line, int col) {
    list[Tree] focus = [];
    bottom-up visit(tr) {
        case t:appl(prod(def, _, _), _): {
            if (isContainedIn(t, line, col) && trim("<t>") != "") focus += t;
        }
    }
    return focus;
}
