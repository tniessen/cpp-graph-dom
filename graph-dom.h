#pragma once

#include <concepts>
#include <ranges>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifndef GRAPH_DOM_NO_ASSERT
#  include <cassert>
#  define GRAPH_DOM_ASSERT(x) assert(x)
#else
#  define GRAPH_DOM_ASSERT(x) ((void)0)
#endif

namespace graph_dom {

// Graph nodes must be hashable objects because they are used as keys of an
// unordered map internally.
template <typename N>
concept graph_node = std::is_object_v<N> && requires (N v) {
  { std::hash<N>{}(v) } -> std::convertible_to<std::size_t>;
};

template <typename N, typename S>
concept successor_function = graph_node<N> && requires (S& s, const N& node) {
  { s(node) } -> std::ranges::range;
  requires std::is_convertible_v<std::ranges::range_value_t<decltype(s(node))>, decltype(node)>;
};

// Abstraction of arbitrary directed graphs.
template <typename G>
concept graph = requires (const G& g, typename G::node_type node) {
  typename G::node_type;
  requires graph_node<typename G::node_type>;
  { g.root() } -> std::convertible_to<typename G::node_type>;
  { g.succ(node) } -> std::ranges::range;
  requires std::is_convertible_v<std::ranges::range_value_t<decltype(g.succ(node))>, typename G::node_type>;
};

template <graph_node N>
class post_dominator_tree;

// Dominator tree implementation based on the algorithm by Lengauer and Tarjan
// as described in "A Fast Algorithm for Finding Dominators in a Flowgraph"
// (1979), see https://doi.org/10.1145/357062.357071.
//
// Currently, only the _simple_ version of the algorithm is implemented.
template <graph_node N>
class dominator_tree {
public:
  // Type of const references to graph nodes.
  using node_ref_type = const N&;
  // Type of const pointers to graph nodes, potentially nullptr.
  using maybe_node_type = const N*;

  // Compute the dominator tree of the given directed graph.
  template <graph G>
  requires std::same_as<typename G::node_type, N>
  explicit dominator_tree(const G& g)
      : dominator_tree(g.root(), [&g](const N& n) { return g.succ(n); }) {}

  // Compute the dominator tree of the given directed graph.
  template <typename S>
  requires successor_function<N, S>
  explicit dominator_tree(const N& root, S&& succ) {
    // Step 1.
    depth_first_search(root, std::forward<S&>(succ));

    for (size_t w = v_.size() - 1; w >= 1; w--) {
      // Step 2.
      for (size_t v : v_[w].pred) {
        size_t u = eval(v);
        if (v_[u].semi < v_[w].semi) {
          v_[w].semi = v_[u].semi;
        }
      }
      v_[v_[w].semi].bucket.insert(w);
      link(v_[w].parent, w);

      // Step 3.
      for (size_t v : v_[v_[w].parent].bucket) {
        size_t u = eval(v);
        v_[v].dom = v_[u].semi < v_[v].semi ? u : *v_[w].parent;
      }
      v_[v_[w].parent].bucket.clear();
    }

    // Step 4.
    for (size_t w = 1; w < v_.size(); w++) {
      if (v_[w].dom != v_[w].semi) {
        v_[w].dom = v_[v_[w].dom].dom;
      }
    }
  }

  // The root node of the dominator tree (i.e., the entry node of the graph).
  [[nodiscard]] node_ref_type root() const { return v_.front().vertex; }

  // Returns whether the given node was reachable from the entry node and thus
  // is part of the dominator tree.
  [[nodiscard]] bool contains(node_ref_type node) const {
    return inv_v_.contains(node);
  }

  // Returns the parent of the given node during the depth-first search
  // traversal of the graph. This is not the same as the immediate dominator.
  [[nodiscard]] maybe_node_type dfs_parent(node_ref_type node) const {
    const auto index_it = inv_v_.find(node);
    if (index_it == inv_v_.end()) return nullptr;
    size_t index = index_it->second;
    const maybe_idx& parent = v_[index].parent;
    return parent.empty() ? nullptr : &v_[*parent].vertex;
  }

  // Returns the immediate dominator of the given node. If the given node is the
  // root node, or if it was not reachable from the root node, then this will
  // return nullptr.
  [[nodiscard]] maybe_node_type immediate_dominator(node_ref_type node) const {
    const auto index_it = inv_v_.find(node);
    if (index_it == inv_v_.end()) return nullptr;
    size_t index = index_it->second;
    const maybe_idx& dom = v_[index].dom;
    return dom.empty() ? nullptr : &v_[*dom].vertex;
  }

  // Returns whether the given node A dominates the given node B.
  //
  // If neither node was reachable from the root node, then this will return
  // false regardless of whether a would dominate b in any other case. That
  // includes the case in which a is equal to b.
  [[nodiscard]]
  bool dominates(node_ref_type a, node_ref_type b, bool strict = false) const {
    // Translate nodes to indices.
    auto inv_a = inv_v_.find(a);
    if (inv_a == inv_v_.end()) return false;
    auto inv_b = inv_v_.find(b);
    if (inv_b == inv_v_.end()) return false;
    size_t index_a = inv_a->second;
    size_t index_b = inv_b->second;

    // Each node dominates itself, but no node strictly dominates itself.
    if (index_a == index_b) return !strict;

    // Walk up the dominator tree, starting from node B, until we either reach
    // node A or the root of the tree.
    size_t index_walk = index_b;
    do {
      const maybe_idx& dom = v_[index_walk].dom;
      if (dom.empty()) return false;
      index_walk = *dom;
    } while (index_walk != index_a);

    return true;
  }

  // Returns whether the given node A strictly dominates the given node B.
  //
  // If neither node was reachable from the root node, then this will return
  // false regardless of whether a would strictly dominate b in any other case.
  [[nodiscard]]
  inline bool strictly_dominates(node_ref_type a, node_ref_type b) const {
    return dominates(a, b, true);
  }

private:
  // Smaller than std::optional<size_t>, at the cost of restricting the domain.
  // Implicit conversion to size_t is allowed if and only if the value is
  // non-empty.
  class maybe_idx {
  public:
    constexpr maybe_idx() : value_(NO_VALUE) {}
    maybe_idx(size_t value) : value_(value) { GRAPH_DOM_ASSERT(!empty()); }

    [[nodiscard]] inline operator size_t() const { return **this; }

    [[nodiscard]] inline size_t operator*() const {
      GRAPH_DOM_ASSERT(!empty());
      return value_;
    }

    [[nodiscard]] inline bool empty() const { return value_ == NO_VALUE; }

  private:
    static constexpr size_t NO_VALUE = static_cast<size_t>(-1);
    size_t value_;
  };

  struct vertex_data {
    N vertex;
    maybe_idx semi;
    maybe_idx label;
    maybe_idx parent;
    std::unordered_set<size_t> pred;
    maybe_idx ancestor;
    std::unordered_set<size_t> bucket;
    maybe_idx dom;

    explicit vertex_data(N v, size_t i)
        : vertex(std::move(v)), semi(i), label(i) {}
  };

  template <typename S>
  requires successor_function<N, S>
  size_t depth_first_search(N v_node, S& succ) {
    const size_t v_index = v_.size();
    v_.emplace_back(v_node, v_index);
    GRAPH_DOM_ASSERT(!inv_v_.contains(v_node));
    inv_v_.emplace(v_node, v_index);
    for (const auto& w : succ(v_node)) {
      size_t w_index;
      if (const auto w_it = inv_v_.find(w); w_it != inv_v_.end()) {
        w_index = w_it->second;
      } else {
        w_index = depth_first_search(w, succ);
        v_[w_index].parent = v_index;
      }
      v_[w_index].pred.insert(v_index);
    }
    return v_index;
  }

  inline void link(size_t v, size_t w) {
    v_[w].ancestor = v;
  }

  inline void compress(size_t v_index) {
    auto& v = v_[v_index];
    if (!v_[v.ancestor].ancestor.empty()) {
      compress(v.ancestor);
      if (v_[v_[v.ancestor].label].semi < v_[v.label].semi) {
        v.label = v_[v.ancestor].label;
      }
      v.ancestor = v_[v.ancestor].ancestor;
    }
  }

  [[nodiscard]] inline size_t eval(size_t v) {
    GRAPH_DOM_ASSERT(v < v_.size());
    if (v_[v].ancestor.empty()) {
      return v;
    } else {
      compress(v);
      return v_[v].label;
    }
  }

  std::vector<vertex_data> v_;
  std::unordered_map<N, size_t> inv_v_;

  friend class post_dominator_tree<N>;
};

// Deduction guide for the dominator_tree constructor.
template <graph G>
dominator_tree(const G& g) -> dominator_tree<typename G::node_type>;

// Post-dominator tree.
template <graph_node N>
class post_dominator_tree {
public:
  using node_ref_type = const N&;
  using maybe_node_type = const N*;

  // Compute the post-dominator tree from the given dominator tree by reusing
  // some of the information gathered during the dominator tree construction.
  // The given dominator tree must contain the exit node of the graph, which is
  // the root of the post-dominator tree.
  explicit post_dominator_tree(const dominator_tree<N>& dom_tree, N&& exit)
      : dom_tree_(compute_reverse_tree(dom_tree, std::forward<const N&>(exit))) {}

  // The root node of the post-dominator tree (i.e., the exit node of the graph).
  [[nodiscard]] node_ref_type root() const { return dom_tree_.root(); }

  // Returns whether the given node was reachable from the exit node and thus
  // is part of the post-dominator tree.
  [[nodiscard]] bool contains(node_ref_type node) const {
    return dom_tree_.contains(node);
  }

  // Returns the parent of the given node during the depth-first search
  // traversal of the graph. This is not the same as the immediate
  // post-dominator.
  [[nodiscard]] maybe_node_type dfs_parent(node_ref_type node) const {
    return dom_tree_.dfs_parent(node);
  }

  // Returns the immediate post-dominator of the given node. If the given node
  // is the exit node, or if it was not reachable from the exit node, then this
  // will return nullptr.
  [[nodiscard]] maybe_node_type immediate_post_dominator(node_ref_type node) const {
    return dom_tree_.immediate_dominator(node);
  }

  // Returns whether the given node A post-dominates the given node B.
  //
  // If neither node was reachable from the root node, then this will return
  // false regardless of whether a would post-dominate b in any other case. That
  // includes the case in which a is equal to b.
  [[nodiscard]]
  bool post_dominates(node_ref_type a, node_ref_type b, bool strict = false) const {
    return dom_tree_.dominates(a, b, strict);
  }

  // Returns whether the given node A strictly post-dominates the given node B.
  //
  // If neither node was reachable from the root node, then this will return
  // false regardless of whether a would strictly post-dominate b in any other
  // case.
  [[nodiscard]]
  inline bool strictly_post_dominates(node_ref_type a, node_ref_type b) const {
    return post_dominates(a, b, true);
  }

private:
  static inline dominator_tree<N> compute_reverse_tree(
      const dominator_tree<N>& dom_tree, const N& exit) {
    GRAPH_DOM_ASSERT(dom_tree.contains(exit));
    return dominator_tree<N>(exit, [&dom_tree](node_ref_type node) {
      size_t index = dom_tree.inv_v_.at(node);
      return dom_tree.v_[index].pred | std::views::transform(
          [&dom_tree](size_t i) { return std::cref(dom_tree.v_[i].vertex); });
    });
  }

  dominator_tree<N> dom_tree_;
};

// Deduction guide for the post_dominator_tree constructor for the case where
// the exit node is a non-const pointer but N is a const pointer.
template <graph_node N>
post_dominator_tree(const dominator_tree<N>& dom_tree,
                    std::remove_const_t<std::remove_pointer_t<N>>*&& exit)
    -> post_dominator_tree<N>;

}  // namespace graph_dom
