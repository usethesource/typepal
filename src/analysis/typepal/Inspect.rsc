module analysis::typepal::Inspect

import analysis::typepal::Collector;
import String;
import IO;
import ValueIO;
import Node;
import Map;

void show(loc tmodelLoc){

    if(!endsWith(tmodelLoc.path, ".tpl")){
        println("Can only show files with `tpl` extension");
        return;
    }
    tm = readBinaryValueFile(#TModel, tmodelLoc);
    //iprintln(tm.store);
    //iprintln(tm.paths);
    iprintln(tm.defines);
    for(d <- tm.defines, d.id == "config"){
        println(d, lineLimit=10000); 
    }
}