#undef NDEBUG

#include "../graph-dom.h"

#include <bitset>
#include <cassert>
#include <memory>
#include <string>
#include <string_view>

// A very simple graph implementation whose nodes are unsigned integers, and
// the list of successors of each node is explicitly stored as a vector.
template <std::unsigned_integral T>
class uint_successor_graph {
public:
  using node_type = T;

  uint_successor_graph(node_type root,
                       std::vector<std::vector<node_type>>&& successors)
      : root_(root), nodes_(std::move(successors)) {
    assert(root < nodes_.size());
  }

  [[nodiscard]] node_type root() const {
    return root_;
  }

  [[nodiscard]] const std::vector<node_type>& succ(node_type index) const {
    assert(index < nodes_.size());
    return nodes_[index];
  }

private:
  node_type root_;
  std::vector<std::vector<node_type>> nodes_;
};

// A very simple graph implementation whose nodes are unsigned integers, and
// the list of successors of each node is explicitly stored as a vector.
template <size_t MAX_NODE_EXCL, std::unsigned_integral T>
class uint_bitset_graph {
public:
  using node_type = T;

  uint_bitset_graph(node_type root) : root_(root) {
    assert(root < MAX_NODE_EXCL);
  }

  void add_edge(node_type from, node_type to) {
    assert(from < MAX_NODE_EXCL && to < MAX_NODE_EXCL);
    nodes_.at(from).set(to);
  }

  [[nodiscard]] node_type root() const {
    return root_;
  }

  [[nodiscard]] auto succ(node_type index) const {
    assert(index < MAX_NODE_EXCL);
    const auto& s = nodes_.at(index);
    return std::ranges::views::iota(static_cast<T>(0), MAX_NODE_EXCL)
        | std::views::filter([s](size_t i) { return s.test(i); });
  }

private:
  node_type root_;
  std::array<std::bitset<MAX_NODE_EXCL>, MAX_NODE_EXCL> nodes_;
};

// Very simple graph implementation whose nodes are arbitrary objects as long as
// they are copy constructible. The set of edges is stored as a set of pairs of
// nodes, closely following the mathematical definition of a directed graph.
// However, the order of traversal depends on the order of the edges in the set.
template <std::copy_constructible T>
class edge_set_graph {
public:
  using node_type = T;
  using edge_set_type = std::set<std::pair<node_type, node_type>>;

  edge_set_graph(node_type root, edge_set_type&& edges)
      : root_(std::move(root)), edges_(std::move(edges)) {}

  [[nodiscard]] const node_type& root() const {
    return root_;
  }

  [[nodiscard]] auto succ(const node_type& c) const {
    return edges_
        | std::views::filter([c](const auto& edge) { return edge.first == c; })
        | std::views::transform([](const auto& edge) { return edge.second; });
  }

private:
  node_type root_;
  edge_set_type edges_;
};

// A graph whose nodes are either std::string or std::string_view objects.
template <typename T>
concept is_string_graph =
    graph_dom::graph<T> &&
    (std::same_as<typename T::node_type, std::string> ||
     std::same_as<typename T::node_type, std::string_view>);

class _ptrnode {};

// A graph whose nodes are const pointers to the actual ptrgraph::node objects.
class ptrgraph : public edge_set_graph<const _ptrnode*> {
public:
  using node = _ptrnode;

  ptrgraph(const node* root, edge_set_type&& edges)
      : edge_set_graph(root, std::move(edges)) {}
};

// This example is from the Wikipedia page on dominator trees at the time of
// writing: https://en.wikipedia.org/wiki/Dominator_(graph_theory).
template <std::unsigned_integral T>
static void test_wikipedia_example() {
  uint_successor_graph<T> g(1, {{}, {2}, {3, 4, 6}, {5}, {5}, {2}, {}});

  graph_dom::dominator_tree g_dom(g);
  assert(g_dom.immediate_dominator(1) == nullptr);
  assert(*g_dom.immediate_dominator(2) == 1);
  assert(*g_dom.immediate_dominator(3) == 2);
  assert(*g_dom.immediate_dominator(4) == 2);
  assert(*g_dom.immediate_dominator(5) == 2);
  assert(*g_dom.immediate_dominator(6) == 2);

  for (typename decltype(g)::node_type a = 1; a <= 6; a++) {
    for (typename decltype(g)::node_type b = 1; b <= 6; b++) {
      bool a_strictly_doms_b = (a == 1 || a == 2) && a < b;
      bool a_doms_b = a_strictly_doms_b || a == b;
      assert(g_dom.dominates(a, b) == a_doms_b);
      assert(g_dom.dominates(a, b, true) == a_strictly_doms_b);
      assert(g_dom.strictly_dominates(a, b) == a_strictly_doms_b);
    }
  }
}

template <std::unsigned_integral T>
static void test_wikipedia_example_with_bitset() {
  uint_bitset_graph<7, T> g(1);
  g.add_edge(1, 2);
  g.add_edge(2, 3);
  g.add_edge(2, 4);
  g.add_edge(2, 6);
  g.add_edge(3, 5);
  g.add_edge(4, 5);
  g.add_edge(5, 2);

  graph_dom::dominator_tree g_dom(g);
  assert(g_dom.immediate_dominator(1) == nullptr);
  assert(*g_dom.immediate_dominator(2) == 1);
  assert(*g_dom.immediate_dominator(3) == 2);
  assert(*g_dom.immediate_dominator(4) == 2);
  assert(*g_dom.immediate_dominator(5) == 2);
  assert(*g_dom.immediate_dominator(6) == 2);

  for (typename decltype(g)::node_type a = 1; a <= 6; a++) {
    for (typename decltype(g)::node_type b = 1; b <= 6; b++) {
      bool a_strictly_doms_b = (a == 1 || a == 2) && a < b;
      bool a_doms_b = a_strictly_doms_b || a == b;
      assert(g_dom.dominates(a, b) == a_doms_b);
      assert(g_dom.dominates(a, b, true) == a_strictly_doms_b);
      assert(g_dom.strictly_dominates(a, b) == a_strictly_doms_b);
    }
  }
}

// Example from "Object Code Optimization" by Lowry and Medlock, 1969.
template <typename S>
requires is_string_graph<edge_set_graph<S>>
static void test_lowry_medlock_1969() {
  const edge_set_graph<S> blocks("entry", {
      {"entry", "1"},
      {"1", "2L"}, {"1", "2R"},
      {"2L", "3"}, {"2R", "3"}, {"2R", "6"},
      {"3", "4L"}, {"3", "4R"},
      {"4L", "5"}, {"4R", "5"},
      {"5", "3"}, {"5", "6"},
      {"6", "7"},
      {"7", "7"}, {"7", "8"},
      {"8", "1"}, {"8", "return"}
  });

  graph_dom::dominator_tree dom(blocks);
  assert(dom.immediate_dominator("entry") == nullptr);
  assert(*dom.immediate_dominator("1") == "entry");
  assert(*dom.immediate_dominator("2L") == "1");
  assert(*dom.immediate_dominator("2R") == "1");
  assert(*dom.immediate_dominator("3") == "1");
  assert(*dom.immediate_dominator("4L") == "3");
  assert(*dom.immediate_dominator("4R") == "3");
  assert(*dom.immediate_dominator("5") == "3");
  assert(*dom.immediate_dominator("6") == "1");
  assert(*dom.immediate_dominator("7") == "6");
  assert(*dom.immediate_dominator("8") == "7");
  assert(*dom.immediate_dominator("return") == "8");
}

// Example from "An efficient method of computing static single assignment form"
// by Cytron et al., 1989.
template <typename S>
requires is_string_graph<edge_set_graph<S>>
static void test_cytron_et_al_1989() {
  const edge_set_graph<S> ssa("entry", {
      {"entry", "1"}, {"entry", "exit"},
      {"1", "2"},
      {"2", "3"}, {"2", "7"},
      {"3", "4"}, {"3", "5"},
      {"4", "6"},
      {"5", "6"},
      {"6", "8"},
      {"7", "8"},
      {"8", "9"},
      {"9", "10"}, {"9", "11"},
      {"11", "9"}, {"11", "12"},
      {"12", "exit"}, {"12", "2"}
  });

  const graph_dom::dominator_tree ssa_dom(ssa);
  assert(ssa_dom.immediate_dominator("entry") == nullptr);
  assert(*ssa_dom.immediate_dominator("1") == "entry");
  assert(*ssa_dom.immediate_dominator("2") == "1");
  assert(*ssa_dom.immediate_dominator("3") == "2");
  assert(*ssa_dom.immediate_dominator("7") == "2");
  assert(*ssa_dom.immediate_dominator("8") == "2");
  assert(*ssa_dom.immediate_dominator("4") == "3");
  assert(*ssa_dom.immediate_dominator("5") == "3");
  assert(*ssa_dom.immediate_dominator("6") == "3");
  assert(*ssa_dom.immediate_dominator("9") == "8");
  assert(*ssa_dom.immediate_dominator("10") == "9");
  assert(*ssa_dom.immediate_dominator("11") == "9");
  assert(*ssa_dom.immediate_dominator("12") == "11");
  assert(*ssa_dom.immediate_dominator("exit") == "entry");

  assert(ssa_dom.immediate_dominator("unreachable") == nullptr);
  assert(ssa_dom.dfs_parent("unreachable") == nullptr);
  assert(!ssa_dom.contains("unreachable"));
}

// This example is from "A Fast Algorithm for Finding Dominators in a Flowgraph"
// by Lengauer and Tarjan, 1979.
//
// Because the edge_set_graph reorders edges, the order of DFS traversal might
// differ from the order in the paper, but the dominator relation should be
// computed correctly in any case. See below for a separate test that enforces
// the traversal order from the paper.
static void test_lengauer_tarjan_1979_unordered() {
  edge_set_graph h('R', {
    {'R', 'A'}, {'R', 'B'}, {'R', 'C'},
    {'A', 'D'},
    {'B', 'D'}, {'B', 'E'},
    {'C', 'F'}, {'C', 'G'},
    {'D', 'L'},
    {'E', 'H'},
    {'F', 'I'},
    {'G', 'I'}, {'G', 'J'},
    {'H', 'E'}, {'H', 'K'},
    {'I', 'K'}, {'I', 'K'},
    {'J', 'I'},
    {'K', 'R'}, {'K', 'I'},
    {'L', 'H'}
  });

  graph_dom::dominator_tree dom_tree(h);
  assert(dom_tree.immediate_dominator('R') == nullptr);
  assert(*dom_tree.immediate_dominator('I') == 'R');
  assert(*dom_tree.immediate_dominator('K') == 'R');
  assert(*dom_tree.immediate_dominator('C') == 'R');
  assert(*dom_tree.immediate_dominator('F') == 'C');
  assert(*dom_tree.immediate_dominator('G') == 'C');
  assert(*dom_tree.immediate_dominator('J') == 'G');
  assert(*dom_tree.immediate_dominator('H') == 'R');
  assert(*dom_tree.immediate_dominator('E') == 'R');
  assert(*dom_tree.immediate_dominator('A') == 'R');
  assert(*dom_tree.immediate_dominator('D') == 'R');
  assert(*dom_tree.immediate_dominator('L') == 'D');
  assert(*dom_tree.immediate_dominator('B') == 'R');

  assert(dom_tree.dfs_parent('R') == nullptr);
}

static void test_lengauer_tarjan_1979_ordered() {
  graph_dom::graph_adaptor graph('R', [](char c) -> std::string_view {
    switch (c) {
      case 'R': return "CBA";
      case 'A': return "D";
      case 'B': return "EAD";
      case 'C': return "FG";
      case 'D': return "L";
      case 'E': return "H";
      case 'F': return "I";
      case 'G': return "IJ";
      case 'H': return "KE";
      case 'I': return "K";
      case 'J': return "I";
      case 'K': return "RI";
      case 'L': return "H";
      default: assert(false);
    }
  });
  static_assert(graph_dom::graph<decltype(graph)>);
  static_assert(std::is_same_v<typename decltype(graph)::node_type, char>);
  assert(graph.root() == 'R');

  graph_dom::dominator_tree dom_tree(graph);
  assert(dom_tree.dfs_parent('R') == nullptr);
  assert(*dom_tree.dfs_parent('C') == 'R');
  assert(*dom_tree.dfs_parent('F') == 'C');
  assert(*dom_tree.dfs_parent('I') == 'F');
  assert(*dom_tree.dfs_parent('K') == 'I');
  assert(*dom_tree.dfs_parent('G') == 'C');
  assert(*dom_tree.dfs_parent('J') == 'G');
  assert(*dom_tree.dfs_parent('B') == 'R');
  assert(*dom_tree.dfs_parent('E') == 'B');
  assert(*dom_tree.dfs_parent('H') == 'E');
  assert(*dom_tree.dfs_parent('A') == 'B');
  assert(*dom_tree.dfs_parent('D') == 'A');
  assert(*dom_tree.dfs_parent('L') == 'D');

  assert(dom_tree.immediate_dominator('R') == nullptr);
  assert(*dom_tree.immediate_dominator('I') == 'R');
  assert(*dom_tree.immediate_dominator('K') == 'R');
  assert(*dom_tree.immediate_dominator('C') == 'R');
  assert(*dom_tree.immediate_dominator('F') == 'C');
  assert(*dom_tree.immediate_dominator('G') == 'C');
  assert(*dom_tree.immediate_dominator('J') == 'G');
  assert(*dom_tree.immediate_dominator('H') == 'R');
  assert(*dom_tree.immediate_dominator('E') == 'R');
  assert(*dom_tree.immediate_dominator('A') == 'R');
  assert(*dom_tree.immediate_dominator('D') == 'R');
  assert(*dom_tree.immediate_dominator('L') == 'D');
  assert(*dom_tree.immediate_dominator('B') == 'R');
}

static void test_cfg_loop() {
  ptrgraph::node init, loop_head, loop_body, exit;
  ptrgraph loop(&init, {
      {&init, &loop_head},
      {&loop_head, &loop_body},
      {&loop_head, &exit},
      {&loop_body, &loop_head}
  });

  graph_dom::dominator_tree loop_dom(loop);
  assert(loop_dom.immediate_dominator(&init) == nullptr);
  assert(*loop_dom.immediate_dominator(&loop_head) == &init);
  assert(*loop_dom.immediate_dominator(&loop_body) == &loop_head);
  assert(*loop_dom.immediate_dominator(&exit) == &loop_head);

  assert(loop_dom.strictly_dominates(&init, &loop_head));
  assert(loop_dom.strictly_dominates(&loop_head, &loop_body));
  assert(!loop_dom.dominates(&loop_body, &exit));
  assert(loop_dom.strictly_dominates(&loop_head, &exit));

  ptrgraph::node unreachable;
  assert(loop_dom.immediate_dominator(&unreachable) == nullptr);
  assert(loop_dom.dfs_parent(&unreachable) == nullptr);
  assert(!loop_dom.contains(&unreachable));
}

static void test_cfg_if_then_else() {
  ptrgraph::node init, cond, then_branch, else_branch, merge, exit;
  ptrgraph if_else(&init, {
      {&init, &cond},
      {&cond, &then_branch}, {&cond, &else_branch},
      {&then_branch, &merge},
      {&else_branch, &merge},
      {&merge, &exit}
  });

  graph_dom::dominator_tree if_else_dom(if_else);
  assert(if_else_dom.immediate_dominator(&init) == nullptr);
  assert(*if_else_dom.immediate_dominator(&cond) == &init);
  assert(*if_else_dom.immediate_dominator(&then_branch) == &cond);
  assert(*if_else_dom.immediate_dominator(&else_branch) == &cond);
  assert(*if_else_dom.immediate_dominator(&merge) == &cond);
  assert(*if_else_dom.immediate_dominator(&exit) == &merge);

  assert(!if_else_dom.contains(nullptr));
}

static void test_cfg_self_loop() {
  ptrgraph::node init, self;
  ptrgraph self_loop(&init, {{&init, &self}, {&self, &self}});

  graph_dom::dominator_tree self_loop_dom(self_loop);
  assert(self_loop_dom.immediate_dominator(&init) == nullptr);
  assert(*self_loop_dom.immediate_dominator(&self) == &init);

  assert(self_loop_dom.dominates(&init, &self));
  assert(self_loop_dom.dominates(&self, &self));
  assert(!self_loop_dom.strictly_dominates(&self, &self));
}

// Example based on Figure 1.1 from the master's thesis "Algorithms for Finding
// Dominators in Directed Graphs" by Henrik Knakkegaard Christensen at Aarhus
// University, 2016.
static void test_knakkegaard_christensen_2016_fig_1_1() {
  edge_set_graph fig_1_1('C', {
      {'A', 'B'}, {'A', 'F'},
      {'C', 'D'}, {'C', 'G'},
      {'D', 'A'}, {'D', 'H'},
      {'G', 'E'}, {'G', 'I'},
      {'H', 'J'},
      {'I', 'J'},
      {'J', 'K'},
      {'K', 'C'}
  });

  graph_dom::dominator_tree fig_1_1_dom(fig_1_1);
  assert(*fig_1_1_dom.immediate_dominator('A') == 'D');
  assert(*fig_1_1_dom.immediate_dominator('B') == 'A');
  assert(fig_1_1_dom.immediate_dominator('C') == nullptr);
  assert(*fig_1_1_dom.immediate_dominator('D') == 'C');
  assert(*fig_1_1_dom.immediate_dominator('E') == 'G');
  assert(*fig_1_1_dom.immediate_dominator('F') == 'A');
  assert(*fig_1_1_dom.immediate_dominator('G') == 'C');
  assert(*fig_1_1_dom.immediate_dominator('H') == 'D');
  assert(*fig_1_1_dom.immediate_dominator('I') == 'G');
  assert(*fig_1_1_dom.immediate_dominator('J') == 'C');
  assert(*fig_1_1_dom.immediate_dominator('K') == 'J');
}

// Example based on Figure 2.4 from the master's thesis "Algorithms for Finding
// Dominators in Directed Graphs" by Henrik Knakkegaard Christensen at Aarhus
// University, 2016.
static void test_knakkegaard_christensen_2016_fig_2_4() {
  edge_set_graph fig_2_4('A', {
      {'A', 'B'}, {'A', 'C'},
      {'B', 'D'},
      {'C', 'E'}, {'C', 'F'},
      {'E', 'B'},
      {'F', 'D'}
  });

  graph_dom::dominator_tree fig_2_4_dom(fig_2_4);
  assert(fig_2_4_dom.immediate_dominator('A') == nullptr);
  assert(*fig_2_4_dom.immediate_dominator('B') == 'A');
  assert(*fig_2_4_dom.immediate_dominator('C') == 'A');
  assert(*fig_2_4_dom.immediate_dominator('D') == 'A');
  assert(*fig_2_4_dom.immediate_dominator('E') == 'C');
  assert(*fig_2_4_dom.immediate_dominator('F') == 'C');
}

static void test_single_node() {
  edge_set_graph<char> single_node('A', {});

  graph_dom::dominator_tree dom_tree(single_node);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(dom_tree.contains('A'));
  assert(dom_tree.dominates('A', 'A'));
  assert(!dom_tree.strictly_dominates('A', 'A'));
}

static void test_single_node_explicit_self_loop() {
  edge_set_graph<char> single_node('A', {{'A', 'A'}});

  graph_dom::dominator_tree dom_tree(single_node);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(dom_tree.dominates('A', 'A'));
  assert(!dom_tree.strictly_dominates('A', 'A'));
}

static void test_two_nodes_linear() {
  edge_set_graph<char> two_nodes('A', {{'A', 'B'}});

  graph_dom::dominator_tree dom_tree(two_nodes);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(*dom_tree.dfs_parent('B') == 'A');
}

static void test_three_nodes_branch() {
  edge_set_graph<char> three_nodes('A', {{'A', 'B'}, {'A', 'C'}});

  graph_dom::dominator_tree dom_tree(three_nodes);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'A');
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(*dom_tree.dfs_parent('B') == 'A');
  assert(*dom_tree.dfs_parent('C') == 'A');
}

static void test_cycle() {
  edge_set_graph<char> cycle('A', {{'A', 'B'}, {'B', 'A'}});

  graph_dom::dominator_tree dom_tree(cycle);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(*dom_tree.dfs_parent('B') == 'A');
}

static void test_disconnected_graph() {
  edge_set_graph<char> disconnected('A', {{'A', 'B'}, {'C', 'D'}});

  graph_dom::dominator_tree dom_tree(disconnected);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(!dom_tree.contains('C'));
  assert(!dom_tree.contains('D'));
}

static void test_diamond_graph() {
  edge_set_graph<char> diamond('A', {
      {'A', 'B'}, {'A', 'C'},
      {'B', 'D'}, {'C', 'D'}
  });

  graph_dom::dominator_tree dom_tree(diamond);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'A');
  assert(*dom_tree.immediate_dominator('D') == 'A');
  assert(dom_tree.dfs_parent('A') == nullptr);
  assert(*dom_tree.dfs_parent('B') == 'A');
  assert(*dom_tree.dfs_parent('C') == 'A');
  assert(*dom_tree.dfs_parent('D') == 'B' || *dom_tree.dfs_parent('D') == 'C');
}

static void test_tree_graph() {
  edge_set_graph<char> tree('A', {
      {'A', 'B'}, {'A', 'C'},
      {'B', 'D'}, {'B', 'E'},
      {'C', 'F'}, {'C', 'G'}
  });

  graph_dom::dominator_tree dom_tree(tree);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'A');
  assert(*dom_tree.immediate_dominator('D') == 'B');
  assert(*dom_tree.immediate_dominator('E') == 'B');
  assert(*dom_tree.immediate_dominator('F') == 'C');
  assert(*dom_tree.immediate_dominator('G') == 'C');
}

static void test_graph_with_back_edge() {
  edge_set_graph<char> back_edge('A', {
      {'A', 'B'},
      {'B', 'C'},
      {'C', 'D'},
      {'D', 'B'}
  });

  graph_dom::dominator_tree dom_tree(back_edge);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'B');
  assert(*dom_tree.immediate_dominator('D') == 'C');
}

static void test_complex_graph() {
  edge_set_graph<char> complex('A', {
    {'A', 'B'}, {'B', 'C'}, {'C', 'D'}, {'D', 'E'}, {'E', 'B'}, // Loop 1
    {'C', 'F'}, {'F', 'G'}, {'G', 'H'}, {'H', 'F'},             // Loop 2
    {'D', 'I'}, {'I', 'J'}, {'J', 'K'}, {'K', 'A'}              // Loop 3
  });

  graph_dom::dominator_tree dom_tree(complex);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'B');
  assert(*dom_tree.immediate_dominator('D') == 'C');
  assert(*dom_tree.immediate_dominator('E') == 'D');
  assert(*dom_tree.immediate_dominator('F') == 'C');
  assert(*dom_tree.immediate_dominator('G') == 'F');
  assert(*dom_tree.immediate_dominator('H') == 'G');
  assert(*dom_tree.immediate_dominator('I') == 'D');
  assert(*dom_tree.immediate_dominator('J') == 'I');
  assert(*dom_tree.immediate_dominator('K') == 'J');
}

static void test_complex_graph_using_graph_adaptor() {
  graph_dom::graph_adaptor complex('A', [](char c) -> std::string_view {
    switch (c) {
      case 'A': return "B";
      case 'B': return "C";
      case 'C': return "DF";
      case 'D': return "EI";
      case 'E': return "B";
      case 'F': return "G";
      case 'G': return "H";
      case 'H': return "F";
      case 'I': return "J";
      case 'J': return "K";
      case 'K': return "A";
      default: assert(false);
    }
  });

  graph_dom::dominator_tree dom_tree(complex);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'B');
  assert(*dom_tree.immediate_dominator('D') == 'C');
  assert(*dom_tree.immediate_dominator('E') == 'D');
  assert(*dom_tree.immediate_dominator('F') == 'C');
  assert(*dom_tree.immediate_dominator('G') == 'F');
  assert(*dom_tree.immediate_dominator('H') == 'G');
  assert(*dom_tree.immediate_dominator('I') == 'D');
  assert(*dom_tree.immediate_dominator('J') == 'I');
  assert(*dom_tree.immediate_dominator('K') == 'J');
}

static void test_dead_ends() {
  edge_set_graph<char> dead_ends('A', {
      {'A', 'B'},
      {'B', 'C'},
      {'C', 'D'}, {'C', 'G'},
      {'D', 'E'},
      {'E', 'F'}
  });

  graph_dom::dominator_tree dom_tree(dead_ends);
  assert(dom_tree.immediate_dominator('A') == nullptr);
  assert(*dom_tree.immediate_dominator('B') == 'A');
  assert(*dom_tree.immediate_dominator('C') == 'B');
  assert(*dom_tree.immediate_dominator('D') == 'C');
  assert(*dom_tree.immediate_dominator('E') == 'D');
  assert(*dom_tree.immediate_dominator('F') == 'E');
  assert(*dom_tree.immediate_dominator('G') == 'C');
}

#include <iomanip>
#include <iostream>

int main(int argc, char**) {
  assert(argc == 1);
  unsigned int test_count = 0;

#define TEST(func) \
  static_assert(std::is_same_v<decltype(func), void()>);                    \
  do {                                                                      \
    std::cout                                                               \
        << std::setw(2) << std::setfill(' ') << std::right << ++test_count  \
        << std::setw(60) << std::setfill('.') << std::left << " " #func " " \
        << std::flush;                                                      \
    func();                                                                 \
    std::cout << " ok" << std::endl;                                        \
  } while (0)

  TEST(test_single_node);
  TEST(test_single_node_explicit_self_loop);
  TEST(test_two_nodes_linear);
  TEST(test_three_nodes_branch);
  TEST(test_cycle);
  TEST(test_disconnected_graph);

  TEST(test_diamond_graph);
  TEST(test_tree_graph);
  TEST(test_graph_with_back_edge);
  TEST(test_complex_graph);
  TEST(test_complex_graph_using_graph_adaptor);
  TEST(test_dead_ends);

  TEST(test_cfg_loop);
  TEST(test_cfg_if_then_else);
  TEST(test_cfg_self_loop);

  TEST(test_wikipedia_example<size_t>);
  TEST(test_wikipedia_example<unsigned int>);
  TEST(test_wikipedia_example<unsigned char>);

  TEST(test_wikipedia_example_with_bitset<size_t>);
  TEST(test_wikipedia_example_with_bitset<unsigned int>);
  TEST(test_wikipedia_example_with_bitset<unsigned char>);

  TEST(test_lowry_medlock_1969<std::string_view>);
  TEST(test_lowry_medlock_1969<std::string>);

  TEST(test_lengauer_tarjan_1979_unordered);
  TEST(test_lengauer_tarjan_1979_ordered);

  TEST(test_cytron_et_al_1989<std::string_view>);
  TEST(test_cytron_et_al_1989<std::string>);

  TEST(test_knakkegaard_christensen_2016_fig_1_1);
  TEST(test_knakkegaard_christensen_2016_fig_2_4);

  return 0;
}
