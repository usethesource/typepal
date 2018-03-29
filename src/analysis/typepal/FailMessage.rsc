module analysis::typepal::FailMessage

data FailMessage
    = _error(value src, str msg, list[value] args)
    | _warning(value src, str msg, list[value] args)
    | _info(value src, str msg, list[value] args)
    ;
    
FailMessage error(value src, str msg, value args...) = _error(src, msg, args);
FailMessage warning(value src, str msg, value args...) = _warning(src, msg, args);
FailMessage info(value src, str msg, value args...) = _info(src, msg, args);