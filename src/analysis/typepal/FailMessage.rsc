module analysis::typepal::FailMessage

/*
    FailMessages provide a convenient variation on Rascal's standard Message datatype.
    In the end, FailMessages are reduced to standard Messages.
*/
import Message;
import String;
import util::IDEServices;

data FailMessage(list[CodeAction] fixes = [])
    = fm_error(value src, str msg, list[value] args)
    | fm_warning(value src, str msg, list[value] args)
    | fm_info(value src, str msg, list[value] args)
    ;

FailMessage error(value src, str msg, value args..., list[CodeAction] fixes=[])
    = fixes? ? fm_error(src, msg, args, fixes=fixes): fm_error(src, msg, args);
FailMessage warning(value src, str msg, value args..., list[CodeAction] fixes=[])
    = fixes? ? fm_warning(src, msg, args, fixes=fixes) : fm_warning(src, msg, args);
FailMessage info(value src, str msg, value args..., list[CodeAction] fixes=[])
    = fixes? ?  fm_info(src, msg, args, fixes=fixes) : fm_info(src, msg, args);

str escapePercent(str s) = replaceAll(s, "%", "%%");

FailMessage convert(error(str msg, loc at, fixes=list[CodeAction] fixes))
    = fixes? ? fm_error(at, escapePercent(msg), [], fixes=fixes) : fm_error(src, msg, args);
FailMessage convert(warning(str msg, loc at, fixes=list[CodeAction] fixes))
    = fixes? ? fm_warning(at, escapePercent(msg), [], fixes=fixes) : fm_warning(src, msg, args);
FailMessage convert(info(str msg, loc at, fixes=list[CodeAction] fixes))
    = fixes? ? fm_info(at, escapePercent(msg), [], fixes=fixes) : fm_info(at, escapePercent(msg), []);
