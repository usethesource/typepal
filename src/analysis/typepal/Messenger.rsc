module analysis::typepal::Messenger

import ParseTree;
extend analysis::typepal::AType;

// ---- Some formatting utilities
    
alias TypeProvider = AType(Tree);

AType defaultGetType(Tree t) { throw TypePalUsage("Type of <getLoc(t)> unavailable during collect"); }

str fmt1(AType t, TypeProvider getType)           = prettyPrintAType(t);
str fmt1(str s, TypeProvider getType)             = s;
str fmt1(int n, TypeProvider getType)             = "<n>";
str fmt1(list[value] vals, TypeProvider getType)  = isEmpty(vals) ? "nothing" : intercalateAnd([fmt1(vl, getType) | vl <- vals]);
str fmt1(set[value] vals, TypeProvider getType)   = isEmpty(vals) ? "nothing" : intercalateAnd([fmt1(vl, getType) | vl <- vals]);   
str fmt1(Tree t, TypeProvider getType)            = prettyPrintAType(getType(t));
     
default str fmt1(value v, TypeProvider getType)   = "<v>";
    
str interpolate(str msg, TypeProvider getType, list[value] args){
    int i = 0;
    int a = -1;
    int n = size(msg);
    str result = "";
    while(i < n){
        c = msg[i];
        if(c == "%"){
            i += 1;
            if(i >= n) throw TypePalUsage("% at end of format directive `<msg>`");
            c = msg[i];
            if(c != "%"){
                a += 1;
                if(a >= size(args)) throw TypePalUsage("Given <a> format directives, but only <size(args)> arguments");
            }
            switch(c){
            case "t":
                if(Tree tree := args[a] || AType atype := args[a]){
                    result += "`<fmt1(args[a], getType)>`";
                } else if(list[AType] atypes := args[a]){
                    result += isEmpty(atypes) ? "none" : intercalateAnd(["`<fmt1(at, getType)>`" | at <- atypes]);
                } else if(set[AType] atypes := args[a]){
                    result += isEmpty(atypes) ? "none" : intercalateAnd(["`<fmt1(at, getType)>`" | at <- atypes]);
                } else {
                    throw TypePalUsage("%t format directive requires a Tree, AType or list/set of ATypes, found <args[a]>");
                }
            case "q":
                result += "`<fmt1(args[a], getType)>`";
            case "v":
                result += "<fmt1(args[a], getType)>";
            case "%":
                result += "%";
            default:
                throw TypePalUsage("Unknown format directive `%<c>`");
            }
        } else {
            result += c;
        }
        i += 1;
    }
    if(a != size(args) - 1) throw TypePalUsage("Used <a+1> arguments for format directives, but given <size(args)> arguments");
    return result;
}
    
Message fmt(str severity, value subject, str msg, TypeProvider getType, list[value] args){
    fmsg = interpolate(msg, getType, args);
    loc sloc = |unknown:///|;
    if(loc l := subject) sloc = l;
    else if(Tree t := subject) sloc = getLoc(t);
    else throw TypePalUsage("Subject in error should be have type `Tree` or `loc`, found <typeOf(subject)>");

    switch(severity){
        case "error": return error(fmsg, sloc);
        case "warning": return warning(fmsg, sloc);
        case "info": return info(fmsg, sloc);
        default: throw TypePalInternalError("Unknown severity <severity>");
    }
}
    
Message toMessage(error(value src, str msg), TypeProvider getType) 
    = fmt("error", src, msg, getType, []);
Message toMessage(error(value src, str msg, value arg0), TypeProvider getType) 
    = fmt("error", src, msg, getType, [arg0]);
Message toMessage(error(value src, str msg, value arg0, value arg1), TypeProvider getType) 
    = fmt("error", src, msg, getType, [arg0, arg1]);
Message toMessage(error(value src, str msg, value arg0, value arg1, value arg2), TypeProvider getType) 
    = fmt("error", src, msg, getType, [arg0, arg1, arg2]);
Message toMessage(error(value src, str msg, value arg0, value arg1, value arg2, value arg3), TypeProvider getType) 
    = fmt("error", src, msg, getType, [arg0, arg1, arg2, arg3]);
    

Message toMessage(warning(value src, str msg), TypeProvider getType) 
    = fmt("warning", src, msg, getType, []);
Message toMessage(warning(value src, str msg, value arg0), TypeProvider getType) 
    = fmt("warning", src, msg, getType, [arg0]);
Message toMessage(warning(value src, str msg, value arg0, value arg1), TypeProvider getType) 
    = fmt("warning", src, msg, getType, [arg0, arg1]);
Message toMessage(warning(value src, str msg, value arg0, value arg1, value arg2), TypeProvider getType) 
    = fmt("warning", src, msg, getType, [arg0, arg1, arg2]);
Message toMessage(warning(value src, str msg, value arg0, value arg1, value arg2, value arg3), TypeProvider getType) 
    = fmt("warning", src, msg, getType, [arg0, arg1, arg2, arg3]);
  
Message toMessage(info(value src, str msg), TypeProvider getType) 
    = fmt("info", src, msg, getType, []);
Message toMessage(info(value src, str msg, value arg0), TypeProvider getType) 
    = fmt("info", src, msg, getType, [arg0]);
Message toMessage(info(value src, str msg, value arg0, value arg1), TypeProvider getType) 
    = fmt("info", src, msg, getType, [arg0, arg1]);
Message toMessage(info(value src, str msg, value arg0, value arg1, value arg2), TypeProvider getType) 
    = fmt("info", src, msg, getType, [arg0, arg1, arg2]);
Message toMessage(info(value src, str msg, value arg0, value arg1, value arg2), value arg3, TypeProvider getType) 
    = fmt("info", src, msg, getType, [arg0, arg1, arg2, arg3]);