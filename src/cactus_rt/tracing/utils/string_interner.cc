#include "cactus_rt/tracing/utils/string_interner.h"

namespace cactus_rt::tracing::utils {
std::pair<bool, uint64_t> StringInterner::GetId(const std::string_view& s) {
  if (auto it = ids_.find(s); it != ids_.end()) {
    return std::make_pair(false, it->second);
  }

  const auto& copied_str = strings_.emplace_back(s);
  const auto  id = ++current_id_;
  ids_.emplace(copied_str, id);

  return std::make_pair(true, id);
}

std::pair<bool, uint64_t> StringInterner::GetId(const char* s) {
  return GetId(std::string_view{s});
}
}  // namespace cactus_rt::tracing::utils
