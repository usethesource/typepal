module analysis::typepal::Version

import util::SemVer;

private str currentTplVersion = "1.1.0";

bool isValidVersion(str version){
    return equalVersion(version, currentTplVersion);
}

str getCurrentTplVersion() = currentTplVersion;