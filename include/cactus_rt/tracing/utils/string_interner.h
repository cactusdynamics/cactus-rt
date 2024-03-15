#ifndef CACTUS_TRACING_STRING_INTERNER_H_
#define CACTUS_TRACING_STRING_INTERNER_H_

#include <list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

namespace cactus_rt::tracing::utils {

/**
 * @private
 *
 * This class interns strings to become ids so the ids can be written to the
 * trace file to save space.
 *
 * It is designed to convert the same string content to uint64_t. A string could
 * be a const char*, std::string_view or std::string. If const char* is used,
 * the string content is copied and stored in this class the first time to
 * ensure it is not deleted during the lifetime of this class.
 *
 * This class is NOT thread-safe.
 *
 * TODO: is having a list of strings as references manually necessary? Can we
 * not simply have std::string as the map key. When looking up values, does C++
 * convert const char* to string view which has a hash code and thus should find
 * the string?... Why is C++ so confusing for simple stuff? It looks like this
 * feature only exist in C++20 and above? Heterogenous lookup:
 * http://wg21.link/P0919r0.
 *
 * So for now we are stuck with this.
 */
class StringInterner {
  uint64_t                                       current_id_ = 0;
  std::unordered_map<std::string_view, uint64_t> ids_;
  std::list<std::string>                         strings_;

 public:
  std::pair<bool, uint64_t> GetId(const std::string_view& s);
  std::pair<bool, uint64_t> GetId(const char* s);

  size_t Size() const {
    return strings_.size();
  };
};
}  // namespace cactus_rt::tracing::utils

#endif
