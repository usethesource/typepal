module analysis::typepal::LocationChecks

import Location;
// Generalized versions of isContainedIn and isBefore that take
// a logical -> physical mapping into account.
bool isContainedIn(loc inner, loc outer, map[loc,loc] m)
    = isContainedIn(inner in m ? m[inner] : inner, outer in m ? m[outer] : outer);

bool isBefore(loc inner, loc outer, map[loc,loc] m)
    = isBefore(inner in m ? m[inner] : inner, outer in m ? m[outer] : outer);