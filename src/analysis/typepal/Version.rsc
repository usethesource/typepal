module analysis::typepal::Version

import util::SemVer;

private str currentTplVersion = "2.0.0";

bool isValidTplVersion(str version){
    return equalVersion(version, currentTplVersion);
}

str getCurrentTplVersion() = currentTplVersion;