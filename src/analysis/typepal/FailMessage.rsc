module analysis::typepal::FailMessage

import Message;
import String;

data FailMessage
    = _error(value src, str msg, list[value] args)
    | _warning(value src, str msg, list[value] args)
    | _info(value src, str msg, list[value] args)
    ;
    
FailMessage error(value src, str msg, value args...) = _error(src, msg, args);
FailMessage warning(value src, str msg, value args...) = _warning(src, msg, args);
FailMessage info(value src, str msg, value args...) = _info(src, msg, args);

str escapePercent(str s) = replaceAll(s, "%", "%%");

FailMessage convert(error(str msg, loc at)) = _error(at, escapePercent(msg), []);
FailMessage convert(warning(str msg, loc at)) = _warning(at, escapePercent(msg), []);
FailMessage convert(info(str msg, loc at)) = _info(at, escapePercent(msg), []);