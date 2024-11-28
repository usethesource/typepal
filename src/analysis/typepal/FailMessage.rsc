@license{
Copyright (c) 2017, Paul Klint
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
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

FailMessage convert(m: error(str msg, loc at))
    = m.fixes? ? fm_error(at, escapePercent(msg), [], fixes=m.fixes) : fm_error(at, escapePercent(msg), []);
FailMessage convert(m: warning(str msg, loc at))
    = m.fixes? ? fm_warning(at, escapePercent(msg), [], fixes=m.fixes) : fm_warning(at,  escapePercent(msg), []);
FailMessage convert(m:info(str msg, loc at))
    = m.fixes? ? fm_info(at, escapePercent(msg), [], fixes=m.fixes) : fm_info(at, escapePercent(msg), []);
