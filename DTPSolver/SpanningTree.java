package DTPSolver;

import java.util.List;
import java.util.Set;

public class SpanningTree {
    final public Set<Edge> tree_edges;//多态；
    public double tree_weight;
    public Set<Vertex> leaves = null;//叶子
//    List<Edge> tree_sortedAllEdges;
    SpanningTree(Set<Edge> edges, double weight) {
        tree_edges = edges;
        tree_weight = weight;
    }

}
