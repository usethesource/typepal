module analysis::typepal::Exception

/*
    Exceptions that are used by TypePal
*/

extend analysis::typepal::FailMessage;

data RuntimeException
    = TypePalUsage(str reason)                      // TypePal used incorrectly
    | TypePalUsage(str reason, list[loc] details)   // TypePal used incorrectly, with additional details
    | TypePalInternalError(str reason)              // TypePal internal error
    | TypeUnavailable()                             // Type is not available: used in control flow of solver
    | checkFailed(list[FailMessage] msgs)           // Type check failed: used in control flow of solver
    | wrongTPLVersion(str reason)
    ;
    
data Exception
    = NoBinding()
    | AmbiguousDefinition(set[loc] definitions)
    ;