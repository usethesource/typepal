module analysis::typepal::FailMessage

/*
    FailMessages provide a convenient variation on Rascal's standard Message datatype. 
    In the end, FailMessages are reduced to standard Messages.
*/
import Message;
import String;

data FailMessage
    = fm_error(value src, str msg, list[value] args)
    | fm_warning(value src, str msg, list[value] args)
    | fm_info(value src, str msg, list[value] args)
    ;
    
FailMessage error(value src, str msg, value args...) = fm_error(src, msg, args);
FailMessage warning(value src, str msg, value args...) = fm_warning(src, msg, args);
FailMessage info(value src, str msg, value args...) = fm_info(src, msg, args);

str escapePercent(str s) = replaceAll(s, "%", "%%");

FailMessage convert(error(str msg, loc at)) = fm_error(at, escapePercent(msg), []);
FailMessage convert(warning(str msg, loc at)) = fm_warning(at, escapePercent(msg), []);
FailMessage convert(info(str msg, loc at)) = fm_info(at, escapePercent(msg), []);