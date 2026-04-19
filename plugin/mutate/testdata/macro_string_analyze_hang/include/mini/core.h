#pragma once

#include <type_traits>

namespace mini {
struct compile_string {};

template <typename T>
using remove_cvref_t = typename std::remove_cv<typename std::remove_reference<T>::type>::type;

template <typename Char>
struct basic_string_view {
  const Char* data;
  constexpr basic_string_view(const Char* d) : data(d) {}
};

namespace detail {
template <typename Char>
constexpr basic_string_view<Char> compile_string_to_view(const Char* s) {
  return basic_string_view<Char>(s);
}
}  // namespace detail
}  // namespace mini

#define MINI_STRING_IMPL(s, base)                                          \
  [] {                                                                     \
    struct MINI_COMPILE_STRING : base {                                    \
      using char_type = mini::remove_cvref_t<decltype(s[0])>;              \
      constexpr operator mini::basic_string_view<char_type>() const {      \
        return mini::detail::compile_string_to_view<char_type>(s);         \
      }                                                                    \
    };                                                                     \
    return MINI_COMPILE_STRING();                                          \
  }()

#define MINI_STRING(s) MINI_STRING_IMPL(s, mini::compile_string)
