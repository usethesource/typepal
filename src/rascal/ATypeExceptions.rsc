module rascal::ATypeExceptions

import Exception;
import rascal::AType;

data RuntimeException
    = invalidMatch(str varName, AType typeLub, AType typeBound)
    | invalidMatch(AType targetType, AType sourceType)
    | invalidInstantiation()
    ;