package DTPSolver;

import java.util.Objects;

public class Edge implements Comparable{
    public Vertex source;
    public Vertex sink;
    public double weight;
    public Edge(Vertex source, Vertex sink, double weight){
        this.source = source;
        this.sink = sink;
        this.weight = weight;
    }

    @Override
    public String toString(){
        return "(" + source + ","+sink+")[" + weight + "]";
    }

    @Override
    public int compareTo(Object o) {
        Edge e = (Edge)o;
        int cmp = Double.compare(weight, e.weight);//按权值从小到大排序
        if( cmp == 0){
            cmp = Integer.compare(source.index, e.source.index);
        }
        if (cmp == 0){
            cmp = Integer.compare(sink.index, e.sink.index);
        }
        return cmp;
    }

    public Vertex getOtherEdgeEnd(Vertex r) {
        // return source == r ?sink :source;
        if(source==r){
            return  sink;
        }
        else{
            return  source;
        }
    }
}
