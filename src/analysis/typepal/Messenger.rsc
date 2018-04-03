module analysis::typepal::Messenger

import ParseTree;
import Exception;
import String;
import Set;
import List;

extend analysis::typepal::AType;
import analysis::typepal::FailMessage;
import analysis::typepal::Utils;

// ---- Message utilities -----------------------------------------------------

// Is inner location textually contained in outer location?
bool containedIn(loc inner, loc outer){
    return inner.path == outer.path && inner.offset >= outer.offset && inner.offset + inner.length <= outer.offset + outer.length;
}

list[Message] sortMostPrecise(list[Message] messages)
    = sort(messages, bool (Message a, Message b) {
        loc al = a.at;
        loc bl = b.at;
        if(al.length? && al.top? && bl.length? && bl.top?)
            return (al.length / 10) < (bl.length / 10) || al.top < bl.top;
        return al.path < bl.path;
    });
 
bool alreadyReported(list[Message] messages, loc src) {
    try 
        return !isEmpty(messages) && any(msg <- messages, containedIn(msg.at, src));
    catch UnavailableInformation(): 
        return false;
}

// ---- Formatting utilities --------------------------------------------------

str intercalateAnd(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " and " + strs[-1];
      };
}

str intercalateOr(list[str] strs){
    switch(size(strs)){
      case 0: return "";
      case 1: return strs[0];
      default: 
              return intercalate(", ", strs[0..-1]) + " or " + strs[-1];
      };
}
    
alias TypeProvider = AType(Tree); // Generic provider of types during formatting

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
                //result += "`<fmt1(args[a], getType)>`";
                 if(Tree tree := args[a] || AType atype := args[a]){
                    result += "`<fmt1(args[a], getType)>`";
                } else if(list[value] vals := args[a]){
                    result += isEmpty(vals) ? "none" : intercalateAnd(["`<fmt1(at, getType)>`" | at <- vals]);
                } else if(set[value] vals := args[a]){
                    result += isEmpty(vals) ? "none" : intercalateAnd(["`<fmt1(at, getType)>`" | at <- vals]);
                } else {
                    result += "`<fmt1(args[a], getType)>`";
                   //throw TypePalUsage("%q format directive requires a Tree, AType or list/set of ATypes, found <args[a]>");
                }
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
    
Message toMessage(_error(value src, str msg, list[value] args), TypeProvider getType) 
    = fmt("error", src, msg, getType, args);

Message toMessage(_warning(value src, str msg, list[value] args), TypeProvider getType) 
    = fmt("warning", src, msg, getType, args);
    
Message toMessage(_info(value src, str msg, list[value] args), TypeProvider getType) 
    = fmt("info", src, msg, getType, args);