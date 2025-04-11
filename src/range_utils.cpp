#include "range_utils.h"

namespace range_utils {
    ident_reduction<std::string> join(const std::string &delimiter) {
        // Not particularly efficient, but good enough for logging
        return reduce<std::string>([=](const std::string &a, const std::string &b){ return a + delimiter + b; }, "");
    }
}
