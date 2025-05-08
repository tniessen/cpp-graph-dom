# cpp-graph-dom

This is a tiny, header-only C++20 implementation of the [dominator tree](https://en.wikipedia.org/wiki/Dominator_(graph_theory))
algorithm by Lengauer and Tarjan as described in
["A Fast Algorithm for Finding Dominators in a Flowgraph" (1979)](https://doi.org/10.1145/357062.357071).

This library intentionally does not provide an implementation of directed
graphs. Any data structure that satisfies the concept `graph_dom::graph` can be
used. Alternatively, the `dominator_tree()` constructor can be given an entry
node and an object that satisfies the concept `graph_dom::successor_function`.
