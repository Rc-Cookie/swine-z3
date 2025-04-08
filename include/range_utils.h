#pragma once

#include <functional>
#include <ranges>
#include <optional>
#include <z3++.h>

namespace range_utils {

    template<typename C>
    struct collector {
    };

    struct first_reduction {
    };

    template<typename T, bool min>
    struct minmax_helper {
        const std::function<bool(const T &a, const T &b)> less_than;
    };

    template<typename T>
    struct reduction {
        const std::function<const T(const T &a, const T &b)> reduction;
    };

    template<typename T>
    struct ident_reduction {
        const std::function<const T(const T &a, const T &b)> reduction;
        const std::function<const T()> ident;
    };

    struct _rangify {
    };



    template <typename Container, std::ranges::range R>
    requires std::convertible_to<std::ranges::range_value_t<R>, typename Container::value_type>
    Container operator|(R&& r, collector<Container>) {
        return Container{r.begin(), r.end()};
    }

    template <std::ranges::range R>
    std::optional<std::ranges::range_value_t<R>> operator|(R&& r, first_reduction) {
        for(const auto& v : r)
            return v;
        return {};
    }

    template <std::ranges::range R, bool min>
    std::optional<std::ranges::range_value_t<R>> operator|(R&& r, const minmax_helper<std::ranges::range_value_t<R>, min> &args) {
        std::optional<std::ranges::range_value_t<R>> res;
        for(const auto &t : r)
        if(!res || args.less_than(t, *res) == min)
        res = t;
        return res;
    }

    template <std::ranges::range R>
    std::ranges::range_value_t<R> operator|(R&& r, const ident_reduction<std::ranges::range_value_t<R>> &args) {
    std::optional<std::ranges::range_value_t<R>> res;
    for(const auto &t : r)
    res = res ? args.reduction(*res, t) : t;
    return res ? *res : args.ident();
    }

    template <std::ranges::range R>
    std::optional<std::ranges::range_value_t<R>> operator|(R&& r, const reduction<std::ranges::range_value_t<R>> &args) {
    std::optional<std::ranges::range_value_t<R>> res;
    for(const auto &t : r)
    res = res ? args.reduction(*res, t) : t;
    return res;
    }

    std::vector<z3::expr> operator|(const z3::expr_vector &vec, _rangify);

    /**
     * A range operation that collects the contents of the range into the given type of container.
     * The default implementation simply returns "Container{r.begin(), r.end()}" for a range r.
     *
     * @tparam Container The type of container to collect into
     */
    template <std::ranges::range Container>
    requires (!std::ranges::view<Container>)
    auto to() {
        return collector<Container>{};
    }

    /**
     * Shorthand for to<std::vector<Content>>(). A range operation that collects the contents of
     * the range into a std::vector.
     *
     * @tparam Content The content type for the resulting vector
     */
    template <typename Content>
    auto to_vec() {
        return collector<std::vector<Content>>{};
    }

    /**
     * Shorthand for to<std::vector<std::pair<Key, Value>>>(). A range operation that collects the
     * contents of the range (which must be convertible to pairs) into a std::vector.
     *
     * @tparam Key The type of "first" of the pairs to collect
     * @tparam Value The type of "second" of the pairs to collect, defaults to the same type as "Key"
     */
    template <typename Key, typename Value = Key>
    auto to_pairs() {
        return collector<std::vector<std::pair<Key, Value>>>{};
    }

    /**
     * A range operation that selects the first element of the range and discards the rest. If
     * the range is empty, it returns an empty optional.
     * */
    inline constexpr auto first = first_reduction();

    /**
     * An operation which may be overloaded for specific range-incompatible types to convert them
     * into ranges, to then further be applied regular range operations.
     */
    inline constexpr auto rangify = _rangify();

    // Default "less than" operation
    template <typename T>
    bool _less(const T &a, const T &b) {
        return a < b;
    }

    // Default "plus" operation
    template <typename T>
    T _plus(const T &a, const T &b) {
        return a + b;
    }

    // Default "multiply" operation
    template <typename T>
    T _mult(const T &a, const T &b) {
        return a * b;
    }

    /**
     * Creates a range operation that reduces all elements from the range to a single element,
     * from left to right (sometimes also called fold or foldl), by applying the given function
     * repeatedly until only one element is left. If the range is empty, an empty optional will
     * be returned.
     *
     * @tparam T The type of ranges to operate on
     * @param reduction The reduction function
     */
    template <typename T>
    reduction<T> reduce(const std::function<const T(const T &a, const T &b)> reduction) {
        return { reduction };
    }

    /**
     * Creates a range operation that reduces all elements from the range to a single element,
     * from left to right (sometimes also called fold or foldl), by applying the given function
     * repeatedly until only one element is left. If the range is empty (any only if so), the
     * given "ident" function will be invoked instead and that result will be returned.
     *
     * @tparam T The type of ranges to operate on
     * @param reduction The reduction function
     * @param ident A supplied for a default value if the range is empty
     */
    template <typename T>
    ident_reduction<T> reduce_or_get(const std::function<const T(const T &a, const T &b)> reduction, const std::function<const T()> &ident) {
        return { .reduction = reduction, .ident = ident };
    }

    /**
     * Creates a range operation that reduces all elements from the range to a single element,
     * from left to right (sometimes also called fold or foldl), by applying the given function
     * repeatedly until only one element is left. If the range is empty, the "ident" default
     * value will be returned instead.
     *
     * @tparam T The type of ranges to operate on
     * @param reduction The reduction function
     * @param ident The default value to return if the range is empty
     */
    template <typename T>
    ident_reduction<T> reduce(const std::function<const T(const T &a, const T &b)> reduction, const T &ident) {
        return reduce_or_get<T>(reduction, [&](){ return ident; });
    }

    /**
     * Creates a range operation that reduces all elements from the range to a single element,
     * from left to right (sometimes also called fold or foldl), by applying the given function
     * repeatedly until only one element is left. If the range is empty, the "ident" default
     * value will be returned instead.
     *
     * @tparam T The type of ranges to operate on
     * @param reduction The reduction function
     * @param ident The default value to return if the range is empty
     */
    template <typename T>
    ident_reduction<T> reduce(const std::function<const T(const T &a, const T &b)> reduction, T &&ident) {
        return reduce_or_get<T>(reduction, [i = std::move(ident)](){ return i; });
    }

    /**
     * A special kind of reduction, which returns the minimum value from a range, or an empty
     * optional if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     * @param less_than A custom implementation of "<", otherwise the "<" operator will be used
     */
    template <typename T>
    auto min(std::function<bool(const T& a, const T& b)>&& less_than = _less<T>) {
        return reduce<T>([le = std::move(less_than)](auto& a, auto& b) { return le(a, b) ? a : b; });
    }

    /**
     * A special kind of reduction, which returns the minimum value from a range, or an empty
     * optional if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     */
    template <typename T>
    auto min(std::function<bool(const T& a, const T& b)>& less_than) {
        return reduce<T>([&](auto& a, auto& b) { return less_than(a, b) ? a : b; });
    }

    /**
     * A special kind of reduction, which returns the maximum value from a range, or an empty
     * optional if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     * @param less_than A custom implementation of "<", otherwise the "<" operator will be used.
     *                  NOTE that this is still the LESS than operator, despite this returning
     *                  the maximum.
     */
    template <typename T>
    auto max(std::function<bool(const T& a, const T& b)>&& less_than = _less<T>) {
        return reduce<T>([le = std::move(less_than)](auto& a, auto& b) { return le(a, b) ? b : a; });
    }

    /**
     * A special kind of reduction, which returns the maximum value from a range, or an empty
     * optional if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     */
    template <typename T>
    auto max(std::function<bool(const T& a, const T& b)>& less_than) {
        return reduce<T>([&](auto& a, auto& b) { return less_than(a, b) ? b : a; });
    }

    /**
     * A special kind of reduction which returns the sum of all values according to the "+"
     * operator, or the given zero value if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     * @param zero The value to return if the range is empty
     */
    template <typename T>
    auto sum(const T &zero) {
        return reduce<T>(_plus<T>, zero);
    }

    /**
     * A special kind of reduction which returns the sum of all values according to the "+"
     * operator.
     *
     * @tparam T The type of ranges to operate on
     * @param zero The value to return if the range is empty, by default "0".
     */
    template <typename T>
    auto sum(T && zero = 0) {
        return reduce<T>(_plus<T>, zero);
    }

    /**
     * A special kind of reduction which returns the product all values according to the "*"
     * operator, or the given "one" value if the range is empty.
     *
     * @tparam T The type of ranges to operate on
     * @param one The value to return if the range is empty
     */
    template <typename T>
    auto product(const T &one) {
        return reduce<T>(_mult<T>, one);
    }

    /**
     * A special kind of reduction which returns the product all values according to the "*"
     * operator.
     *
     * @tparam T The type of ranges to operate on
     * @param one The value to return if the range is empty, by default "1"
     */
    template <typename T>
    auto product(T && one = 1) {
        return reduce<T>(_mult<T>, one);
    }

    /**
     * A special kind of transform operation, mapping each value x to the pair {x, mapper(x)}.
     *
     * @tparam K The kinds of values to map
     * @tparam V The kinds of values to map to
     * @param mapper The function to apply to each element from the range
     */
    template<typename K, typename V>
    constexpr auto map_to(V(&& mapper)(K &)) {
        return std::views::transform([m = std::move(mapper)](auto k) -> std::pair<K,V> { return { k, m(k) }; });
    }

    /**
     * A special kind of transform operation, mapping each value x to the pair {mapper(x), x}.
     *
     * @tparam K The kinds of values to map
     * @tparam V The kinds of values to map by
     * @param mapper The function to apply to each element from the range
     */
    template<typename K, typename V>
    constexpr auto map_by(K(&& mapper)(V &)) {
        return std::views::transform([m = std::move(mapper)](auto v) -> std::pair<K,V> { return { m(v), v }; });
    }

    /**
     * A special kind of transform operation, mapping each value x to the pair {key_mapper(x), value_mapper(x)}.
     *
     * @tparam I The kinds of values to take as input
     * @tparam K The kinds of keys to map to
     * @tparam V The kinds of values to map to
     * @param key_mapper The function to apply to each element from the range to obtain the key for it
     * @param value_mapper The function to apply to each element from the range to obtain the value for it
     */
    template<typename I, typename K, typename V>
    constexpr auto map(K(&& key_mapper)(I &), V(&& value_mapper)(I &)) {
        return std::views::transform([k = std::move(key_mapper), v = std::move(value_mapper)](auto i) -> std::pair<K,V> { return { k(i), v(i) }; });
    }
}
