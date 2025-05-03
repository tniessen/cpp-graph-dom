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
concept is_node_type = std::is_object_v<N> && requires (N v) {
  { std::hash<N>{}(v) } -> std::convertible_to<std::size_t>;
};

// Abstraction of arbitrary directed graphs.
template <typename G>
concept graph = requires (const G& g, typename G::node_type node) {
  typename G::node_type;
  requires is_node_type<typename G::node_type>;
  { g.root() } -> std::convertible_to<typename G::node_type>;
  { g.succ(node) } -> std::ranges::range;
  requires std::is_convertible_v<std::ranges::range_value_t<decltype(g.succ(node))>, typename G::node_type>;
};

template <is_node_type N, typename S>
class graph_adaptor {
public:
  using node_type = N;

  explicit graph_adaptor(node_type&& root, S&& succ)
      : root_(std::move(root)), succ_(std::move(succ)) {}

  [[nodiscard]] const node_type& root() const { return root_; }

  [[nodiscard]] auto succ(const node_type& node) const { return succ_(node); }

private:
  node_type root_;
  S succ_;
};

// Dominator tree implementation based on the algorithm by Lengauer and Tarjan
// as described in "A Fast Algorithm for Finding Dominators in a Flowgraph"
// (1979), see https://doi.org/10.1145/357062.357071.
//
// Currently, only the _simple_ version of the algorithm is implemented.
template <graph G>
class dominator_tree {
public:
  // Type of const references to graph nodes.
  using node_ref_type = const typename G::node_type&;
  // Type of const pointers to graph nodes, potentially nullptr.
  using maybe_node_type = const typename G::node_type*;

  // Compute the dominator tree of the given directed graph.
  explicit dominator_tree(const G& g) {
    // Step 1.
    depth_first_search(g, g.root());

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
    G::node_type vertex;
    maybe_idx semi;
    maybe_idx label;
    maybe_idx parent;
    std::unordered_set<size_t> pred;
    maybe_idx ancestor;
    std::unordered_set<size_t> bucket;
    maybe_idx dom;

    explicit vertex_data(G::node_type v, size_t i)
        : vertex(std::move(v)), semi(i), label(i) {}
  };

  size_t depth_first_search(const G& g, typename G::node_type v_node) {
    const size_t v_index = v_.size();
    v_.emplace_back(v_node, v_index);
    GRAPH_DOM_ASSERT(!inv_v_.contains(v_node));
    inv_v_.emplace(v_node, v_index);
    for (const auto& w : g.succ(v_node)) {
      size_t w_index;
      if (const auto w_it = inv_v_.find(w); w_it != inv_v_.end()) {
        w_index = w_it->second;
      } else {
        w_index = depth_first_search(g, w);
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
  std::unordered_map<typename G::node_type, size_t> inv_v_;
};

}  // namespace graph_dom
