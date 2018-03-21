module analysis::typepal::FailMessage

data FailMessage
    = error(value src, str msg)
    | error(value src, str msg, value arg0)
    | error(value src, str msg, value arg0, value arg1)
    | error(value src, str msg, value arg0, value arg1, value arg2)
    | error(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    | warning(value src, str msg)
    | warning(value src, str msg, value arg0)
    | warning(value src, str msg, value arg0, value arg1)
    | warning(value src, str msg, value arg0, value arg1, value arg2)
    | warning(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    | info(value src, str msg)
    | info(value src, str msg, value arg0)
    | info(value src, str msg, value arg0, value arg1)
    | info(value src, str msg, value arg0, value arg1, value arg2)
    | info(value src, str msg, value arg0, value arg1, value arg2, value arg3)
    ;