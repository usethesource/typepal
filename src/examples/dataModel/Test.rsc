module examples::dataModel::Test

import examples::dataModel::Syntax;
extend examples::dataModel::Checker;
extend analysis::typepal::TestFramework;

TModel dmTModelForTree(Tree pt){
    return collectAndSolve(pt, config = dmConfig());
}

TModel dmTModelFromName(str mname){
    pt = parse(#start[Program], |project://typepal/src/examples/dataModel/<mname>.dm|).top;
    return dmTModelForTree(pt);
}

value main() {
    tm = dmTModelFromName("example1");
    //iprintln(tm, lineLimit=10000);
    return tm.messages;
}