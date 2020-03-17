module analysis::typepal::Inspect

import analysis::typepal::Collector;
import String;
import IO;
import ValueIO;
 
void show(loc tmodelLoc, str key){

    if(!endsWith(tmodelLoc.path, ".tpl")){
        println("Can only show files with `tpl` extension");
        return;
    }
    tm = readBinaryValueFile(#TModel, tmodelLoc);
    for(/Tree t := tm) iprintln(t);
    //for(d <- tm.defines, d.id == key){
    //    iprintln(d, lineLimit=10000); 
    //}
}