module analysis::typepal::AType

import String;
import List;
import Message;
extend analysis::typepal::ScopeGraph;

// Extend AType for type checking purposes
data AType
    = tvar(loc name)                             // type variable, used for type inference
    | lazyLub(list[AType] atypes)                // lazily computed LUB of a list of types
    | atypeList(list[AType] atypes)              // built-in list-of-ATypes type
    | overloadedAType(rel[Key, IdRole, AType] overloads) // built-in-overloaded type; each key provides an alternative type
    ;

// Pretty print ATypes
str prettyPrintAType(tvar(loc name))                = "typevar(<name>)";
str prettyPrintAType(lazyLub(list[AType] atypes))   = "lub(<atypes>))";
str prettyPrintAType(atypeList(list[AType] atypes)) = size(atypes) == 0 ? "empty list of types" : intercalate(", ", [prettyPrintAType(a) | a <- atypes]);
default str prettyPrintAType(overloadedAType(rel[Key, IdRole, AType] overloads)) 
                                                    = "overloaded: {" + intercalate(", ", [prettyPrintAType(t) | <k, r, t> <- overloads]) + "}";
default str prettyPrintAType(AType tp)              = "<tp>";

// AType utilities
bool isTypeVariable(loc tv) = startsWith(tv.scheme, "typevar+"); 

data RuntimeException
    = checkFailed(set[Message] msgs)
    ;

// Some reporting utilities

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

list[Message] sortMostPrecise(list[Message] messages)
    = sort(messages, bool (Message a, Message b) {
        loc al = a.at;
        loc bl = b.at;
        return (al.length / 10) < (bl.length / 10) || al.top < bl.top;
    });

list[Message] filterMostGlobal(set[Message] messages) = [*messages];
// = { msg | msg <- messages, !any(msg2 <- messages, surrounds(msg2, msg)) };