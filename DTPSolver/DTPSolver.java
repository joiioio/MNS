
package DTPSolver;

import javax.crypto.spec.PSource;
import java.io.*;
import java.sql.SQLOutput;
import java.util.*;
import java.util.stream.Collectors;

// 嵌套版本；

public class DTPSolver {

    final private Random random;

    Graph graph;


    Vertex last_add=null;
    int best_x_size=0;
    int count_over_size=0;
    int count_small_size=0;
    int count_chose_exchang_in_over=0;
    int count_chose_exchang_in_small=0;

    final Set<Vertex> X = new TreeSet<>();//用于存储支配树的节点
    final Set<Vertex> X_plus = new TreeSet<>();//被支配的节点
    final Set<Vertex> X_minu = new TreeSet<>();//未被支配的节点
    SpanningTree tree;

    boolean is_out=true;

    int iter_count = 0;
    long start_time;
    double time_limit = 1000;
//
    Map<Integer, Set<Solution>> solutionPools = new TreeMap<>();
    Map<Integer, Integer> same_sol_again_count = new TreeMap<>();
    int cut_count = 0;
    Solution currBestSol;
    int MAX_FAIL_COUNT = 400;

    double PERTURB_STR_RATIO_MIN = 0.0;
    double PERTURB_STR_RATIO_MAX = 0.0;


    int per_count=0;
    double TTR;
    int MD;
    int[] g_disjointSet;
    boolean[] g_visited;


    public void setTime_limit(double time){
        time_limit = time;
    }



    public DTPSolver(String instance, int seed,int fail_count,double pERTURB_STR_RATIO_MIN,double pERTURB_STR_RATIO_MAX,int md,double ttr ) throws IOException {
        //System.out.println("in decoration");
        random = new Random(seed);

        MAX_FAIL_COUNT=fail_count;
        PERTURB_STR_RATIO_MIN=pERTURB_STR_RATIO_MIN;
        PERTURB_STR_RATIO_MAX=pERTURB_STR_RATIO_MAX;
        MD=md;
        TTR=ttr;
        readInstance(instance);
    }

    public void readInstance(String instance) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(instance));
        String line = br.readLine();
        String[] data = line.split(" ");
        int nodeNum = Integer.parseInt(data[0]);
        g_disjointSet=new int[nodeNum];
        g_visited=new boolean[nodeNum];
        int edgeNum = Integer.parseInt(data[1]);

        graph = new Graph(nodeNum);
        for (int i = 0; i < edgeNum; ++i) {
            line = br.readLine();
            data = line.split(" ");
            int sourceIndex = Integer.parseInt(data[0]);
            int sinkIndex = Integer.parseInt(data[1]);
            double weight = Double.parseDouble(data[2]);
            Vertex source = graph.get_vertex_by_index(sourceIndex);
            if (source == null) {
                source = new Vertex(sourceIndex);
                graph.add_vertex(source);
            }
            Vertex sink = graph.get_vertex_by_index(sinkIndex);
            if (sink == null) {
                sink = new Vertex(sinkIndex);
                graph.add_vertex(sink);
            }
            Edge edge = new Edge(source, sink,weight);
            graph.add_edge(edge);


        }

        br.close();
        graph.trim_to_size();
    }

    private int get_min_index_in_C(double[] C, boolean[] visited){
        var min_index = -1;
        for(int i=0; i<C.length; ++i){
            if(visited[i])continue;
            if(min_index == -1){
                min_index = i;
            }else if(C[i] < C[min_index]){
                min_index = i;
            }
        }
        return min_index;
    }

    private SpanningTree prims_algorithm(){
        double[] C = new double[graph.vertices.length];
        Edge[] E = new Edge[graph.vertices.length];
        boolean[] visited = new boolean[graph.vertices.length];
        Arrays.fill(C, Double.MAX_VALUE);
        Arrays.fill(E, null);
        Arrays.fill(visited, false);

        var tree_edges = new TreeSet<Edge>();
        var tree_weight = 0.0;
        var leaves = new TreeSet<Vertex>();

        while(tree_edges.size() < graph.vertices.length - 1){
            int min_index = get_min_index_in_C(C, visited);
            visited[min_index] = true;
            Vertex source = graph.vertices[min_index];
            if(E[min_index] != null) {
                tree_edges.add(E[min_index]);
                tree_weight += E[min_index].weight;
                leaves.add(source);
                leaves.remove(E[min_index].getOtherEdgeEnd(source));
            }
            for(Edge e : graph.edge_list[source.index]){
                Vertex sink = e.getOtherEdgeEnd(source);
                if(!visited[sink.index] && e.weight < C[sink.index]){
                    C[sink.index] = e.weight;
                    E[sink.index] = e;
                }
            }
        }

        var tree = new SpanningTree(tree_edges, tree_weight);
        tree.leaves = leaves;

        return tree;
    }

    private void init() {
        start_time = System.currentTimeMillis();
        SpanningTree init_tree = prims_algorithm();
        for (Vertex v : graph.vertices) {
            v.degree_to_X = graph.edge_list[v.index].size();
            v.is_in_X = true;
            X.add(v);
        }
        for(Vertex v : init_tree.leaves){
            remove_vertex_from_X(v);
        }
        var candidateEdges = collect_edges_set_in_X();
        tree = calc_spanning_tree(candidateEdges);
        Set<Solution> solSet = new TreeSet<>();
        currBestSol=new Solution(this);
        solSet.add(currBestSol);
        solutionPools.put(X.size(), solSet);
    }


    private void sampling(){
        for(;;){
            Vertex moveOutV = shrink_X();
            if(X_minu.size() == 0){
                var edges = new ArrayList<>(collect_edges_set_in_X());
                tree = calc_spanning_tree(edges);
            }else{
                tree = null;
            }
            boolean res = find_any_feasible_tree();
            if(!res)break;
            var solSet = new TreeSet<Solution>();
            best_x_size=X.size();
            solSet.add(currBestSol);
            solutionPools.put(X.size(), solSet);
            same_sol_again_count.put(X.size(), 0);
        }

    }
    private Solution get_best_sol_from_pool(){
        double best_tree_weight = Double.MAX_VALUE;
        Set<Solution> best_solSet = null;
        for(var solSetEntry : solutionPools.entrySet()){
            Set<Solution> solSet = solSetEntry.getValue();
            Solution sol = solSet.iterator().next();
            if(sol.not_dominated_count > 0) continue;
            double weight = sol.tree.tree_weight;
            if( weight < best_tree_weight){
                best_tree_weight =weight;
                best_solSet = solSet;
            }
        }
        if(best_solSet == null){
            return null;
        }
        var iter = best_solSet.iterator();
        Solution bestSol = iter.next();
        return bestSol;
    }

    private int get_best_solution_X_size(){
        if(solutionPools.isEmpty()){
            return -1;
        }
        double best_weight = Double.MAX_VALUE;
        int best_X_size = 0;
        for(var solSetEntry : solutionPools.entrySet()){
            int X_size = solSetEntry.getKey();
            var sol = solSetEntry.getValue().iterator().next();
            if(sol.tree != null && sol.tree.tree_weight < best_weight){
                best_weight = sol.tree.tree_weight;
                best_X_size = X_size;
            }
        }
        return best_X_size;
    }

    private Solution get_random_solution_in_pool(int X_size){
        var solSet = solutionPools.get(X_size);
        if(solSet == null)return null;
        return get_random_item_in_set(solSet);
    }

    private <T> T get_random_item_in_set(Set<T> set){
        int randi = random.nextInt(set.size());
        var iter = set.iterator();
        T item = iter.next();
        for(int i=0; i < randi; ++i){
            item = iter.next();
        }
        return item;
    }

    private void calc_plus_minu_set(){
        for(Vertex v : graph.vertices){
            v.degree_to_X = 0;
            v.tabu_iter = 0;
            v.is_in_X = X.contains(v);

            for(Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(X.contains(u)){
                    ++v.degree_to_X;


                }

            }
            if(!v.is_in_X) {
                if (v.degree_to_X > 0) {
                    X_plus.add(v);
                } else {
                    X_minu.add(v);
                }
            }
        }
    }

    private void rebuilt_curr_sol(Solution sol){
        X.clear();
        X.addAll(sol.dominating_set);
        X_plus.clear();
        X_minu.clear();
        calc_plus_minu_set();
        tree = sol.tree;
    }

    public Solution solve() throws IOException {
        init();
        sampling();
        local_search();


        return currBestSol;
    }
    private Move get_random_addmove(){
        Vertex iv;
        iv=get_random_item_in_set(X_plus);
        return evaluate_moveAdd(iv);
    }
    private Move get_random_move(){
        Vertex iv, rv;
        do{
            find_cut_vertices();
            iv = get_random_item_in_set(X_plus);
            var rv_candidate = X.stream().filter(v->!v.is_cut).collect(Collectors.toList());
            rv = rv_candidate.get(random.nextInt(rv_candidate.size()));
        }while(is_infeasible_move(iv, rv));
        return evaluate_move(iv, rv, true);
    }

    private void perturb(int strength){
        per_count++;
        Solution sol = get_random_solution_in_pool(best_x_size+random.nextInt(3));
        if(sol==null){
            sol=get_random_solution_in_pool(best_x_size);
        }
        rebuilt_curr_sol(sol);

        for(int i=0; i<strength; ++i){
            Move mv = get_random_move();
            make_move(mv);
        }
        find_cut_vertices();
        check_configuration();
    }

    private Vertex shrink_X() {
        find_cut_vertices();
        Vertex[] non_cut_points = X.stream().filter(v -> !v.is_cut).toArray(size -> new Vertex[size]);
        Vertex rand_remove_vertex = non_cut_points[random.nextInt(non_cut_points.length)];
        remove_vertex_from_X(rand_remove_vertex);
        return rand_remove_vertex;
    }

    private void remove_vertex_from_X(Vertex v) {
        v.is_in_X = false;
        X.remove(v);
        X_plus.add(v);
        for (Edge e : graph.edge_list[v.index]) {
            Vertex u = e.getOtherEdgeEnd(v);
            u.degree_to_X--;
            if (!u.is_in_X && u.degree_to_X == 0) {
                X_plus.remove(u);
                X_minu.add(u);
            }
        }
    }

    private void add_vertex_to_X(Vertex v){
        v.is_in_X = true;
        X_plus.remove(v);
        X.add(v);
        for(Edge e : graph.edge_list[v.index]){
            Vertex u = e.getOtherEdgeEnd(v);
            u.degree_to_X++;
            if(!u.is_in_X && u.degree_to_X == 1){
                X_plus.add(u);
                X_minu.remove(u);
            }
        }

    }

    private ArrayList<Edge> collect_edges_set_in_X(){
        var edges = new ArrayList<Edge>();
        for (Vertex v : X) {
            for (Edge e : graph.edge_list[v.index]) {
                Vertex u = e.getOtherEdgeEnd(v);
                if (u.is_in_X&&u.index < v.index) {
                    edges.add(e);
//                    e.isMute_temp=false;
//                    e.isMute=false;
                }
            }
        }
        return edges;
    }




    private ArrayList<Edge> collect_edges_in_X_after_move_Arr(Vertex addInV, Vertex moveOutV){
        var edges = new ArrayList<Edge>();
        for (Vertex v : X){
            if (v == moveOutV)continue;
            for (Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u.is_in_X && u != moveOutV && u.index < v.index){//避免重复
                    edges.add(e);
                }
            }
        }
        for(Edge e : graph.edge_list[addInV.index]){
            Vertex u = e.getOtherEdgeEnd(addInV);
            if(u.is_in_X && u != moveOutV){
                edges.add(e);
            }
        }

        return edges;
    }
    private ArrayList<Edge> collect_edges_in_X_after_moveAdd_Arry(Vertex addInV){
        var edges =new ArrayList<Edge>();
        for(Vertex v : X){
            for (Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u.is_in_X && u.index < v.index){//避免重复
                    edges.add(e);
                }
            }
        }
        for(Edge e : graph.edge_list[addInV.index]){
            Vertex u = e.getOtherEdgeEnd(addInV);
            if(u.is_in_X ){
                edges.add(e);
            }
        }
        return edges;
    }
    private ArrayList<Edge> collet_eges_in_X_after_moveOut_Arry(Vertex moveOutV){
        var edges = new ArrayList<Edge>();
        for (Vertex v : X){
            if (v == moveOutV)continue;
            for (Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u.is_in_X && u != moveOutV && u.index < v.index){//避免重复
                    edges.add(e);
                }
            }
        }
        return edges;

    }
    private ArrayList<Vertex> get_reduced_candidate_insert_v(){
        var candidates = new ArrayList<Vertex>();

        for(Vertex v : X_minu){
            for(Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u.degree_to_X > 0 && !u.is_in_X){
                    candidates.add(u);
                }
            }
        }
        return candidates;
    }

    private boolean is_infeasible_move(Vertex addInV, Vertex moveOutV){//添加的点只通过删除的点接到x则为不可行的move
        return addInV.degree_to_X == 1 && graph.get_edge_weight(addInV, moveOutV) < Double.MAX_VALUE;
    }

    private Move find_move(boolean is_calc_tree, ArrayList<Vertex> addInVs){
        Move bestMv = new Move(null, null, Integer.MAX_VALUE, null);
        Move bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
        int best_count = 0;
        int best_count_t = 0;
        find_cut_vertices();

        for(Vertex addInV : addInVs){
            for(Vertex moveOutV : X){
                if(moveOutV.is_cut)continue;
                if(is_infeasible_move(addInV,moveOutV)){
                    continue;
                }
                Move mv = evaluate_move(addInV, moveOutV, is_calc_tree);
                if(addInV.tabu_iter <= iter_count) {//未被禁忌
                    int cmp = compare_Move(mv, bestMv);
                    if (cmp < 0) {
                        bestMv = mv;
                        best_count = 1;
                    } else if (cmp == 0) {
                        best_count++;
                        if (random.nextInt(best_count) == 0) {
                            bestMv = mv;//概率选择
                        }
                    }
                }else{
                    int cmp = compare_Move(mv, bestMv_t);
                    if(cmp < 0){
                        bestMv_t = mv;
                        best_count_t = 1;
                    }else if(cmp == 0){
                        best_count_t ++;
                        if(random.nextInt(best_count_t)==0){
                            bestMv_t = mv;
                        }
                    }
                }
            }
        }

        int cmp = compare_Move(bestMv, bestMv_t);
        if(bestMv.addInV == null || cmp > 0 && mv_improves_the_best(bestMv_t)){
            return bestMv_t;
        }else {
            return bestMv;
        }
    }
    private Move find_move(ArrayList<Vertex> addInVs){

        if(X.size()-best_x_size>=MD){
            count_over_size++;
            Move Out_bestMv = new Move(null, null, Integer.MAX_VALUE, null);//用于记录<-a>的最好的结果；
            int  Out_best_count=0;
            find_cut_vertices();


            Move bestMv = new Move(null, null, Integer.MAX_VALUE, null);
            Move bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
            int best_count = 0;
            int best_count_t = 0;
            for(var moveOutV : X){
                //评估单移除
                if(moveOutV.is_cut)continue;
                if(moveOutV.tabu_iter>iter_count)continue;
                Move mv=evaluate_moveOut(moveOutV);

                int cmp= compare_Move(mv,Out_bestMv);
                if(cmp<0){
                    Out_bestMv=mv;
                    Out_best_count=1;
                }else if(cmp==0){
                    Out_best_count++;
                    if(random.nextInt(Out_best_count)==0){
                        Out_bestMv=mv;
                    }
                }
                int delta_plus=mv.delta;
                for(var addInV : addInVs){
                    if(is_infeasible_move(addInV, moveOutV)){
                        continue;
                    }
                    Move mvI= evaluate_move_exchange(addInV,moveOutV,delta_plus);


                    if(addInV.tabu_iter<=iter_count){
                        int  cmpI=compare_Move(mvI, bestMv);
                        if(cmpI<0){
                            bestMv=mvI;
                            best_count=1;
                        }else if(cmpI==0){
                            best_count++;
                            if (random.nextInt(best_count) == 0) {
                                bestMv = mvI;//概率选择
                            }
                        }
                    }else{
                        int cmpI = compare_Move(mvI, bestMv_t);
                        if(cmpI< 0){
                            bestMv_t = mvI;
                            best_count_t = 1;
                        }else if(cmpI == 0){
                            best_count_t ++;
                            if(random.nextInt(best_count_t)==0){
                                bestMv_t = mvI;
                            }
                        }
                    }
                }
            }



            Move best = new Move(null, null, Integer.MAX_VALUE, null);
            int cmpa = compare_Move(bestMv, bestMv_t);
            if(bestMv.addInV == null || cmpa > 0 && mv_improves_the_best(bestMv_t)){
                best = bestMv_t;
            }else {
                best = bestMv;
            }
            if(compare_Move(Out_bestMv,best)==-1) {
                return Out_bestMv;
            }else if(compare_Move(Out_bestMv,best)==1){
                count_chose_exchang_in_over++;
                return best;
            }else{
                if(random.nextInt(2)==0)
                    return Out_bestMv;
                else {
                    count_chose_exchang_in_over++;
                    return best;}
            }

        }
        if(X.size()-best_x_size<=-MD){
            count_small_size--;
            find_cut_vertices();
            Move bestMv = new Move(null, null, Integer.MAX_VALUE, null);
            Move bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
            int best_count = 0;
            int best_count_t = 0;
            for(var moveOutV : X){
                //评估单移除
                if(moveOutV.is_cut)continue;
                if(moveOutV.tabu_iter>iter_count)continue;
                for(var addInV : addInVs){
                    if(is_infeasible_move(addInV, moveOutV)){
                        continue;
                    }
                    Move mvI= evaluate_move(addInV,moveOutV,true);
                    if(addInV.tabu_iter<=iter_count){
                        int  cmpI=compare_Move(mvI, bestMv);
                        if(cmpI<0){
                            bestMv=mvI;
                            best_count=1;
                        }else if(cmpI==0){
                            best_count++;
                            if (random.nextInt(best_count) == 0) {
                                bestMv = mvI;//概率选择
                            }
                        }
                    }else{
                        int cmpI = compare_Move(mvI, bestMv_t);
                        if(cmpI< 0){
                            bestMv_t = mvI;
                            best_count_t = 1;
                        }else if(cmpI == 0){
                            best_count_t ++;
                            if(random.nextInt(best_count_t)==0){
                                bestMv_t = mvI;
                            }
                        }
                    }
                }
            }


            Move best = new Move(null, null, Integer.MAX_VALUE, null);//用于记录<-a,+b>的最好move;
            int cmpa = compare_Move(bestMv, bestMv_t);
            if(bestMv.addInV == null || cmpa > 0 && mv_improves_the_best(bestMv_t)){
                best = bestMv_t;
            }else {
                best = bestMv;
            }

            Move Add_bestMv = new Move(null, null, Integer.MAX_VALUE, null);
            Move Add_bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
            int Add_best_count = 0;
            int Add_best_count_t = 0;
            for(Vertex addInV:addInVs){
                Move mv = evaluate_moveAdd(addInV);
                if(addInV.tabu_iter<=iter_count){
                    int cmp =compare_Move(mv, Add_bestMv);
                    if(cmp < 0){
                        Add_bestMv = mv;
                        Add_best_count = 1;
                    } else if (cmp == 0) {
                        Add_best_count++;
                        if (random.nextInt(Add_best_count) == 0) {
                            Add_bestMv = mv;//概率选择
                        }
                    }
                } else{
                    int cmp = compare_Move(mv, Add_bestMv_t);
                    if(cmp < 0){
                        Add_bestMv_t = mv;
                        Add_best_count_t = 1;
                    }else if(cmp == 0){
                        Add_best_count_t ++;
                        if(random.nextInt(Add_best_count_t)==0){
                            Add_bestMv_t = mv;
                        }
                    }
                }
            }
            Move Add_best=null;
            cmpa=compare_Move(Add_bestMv,Add_bestMv_t);
            if(Add_bestMv.addInV==null||cmpa>0&&mv_improves_the_best(Add_bestMv_t)){
                Add_best = Add_bestMv_t;
            }else {
                Add_best = Add_bestMv;
            }
            if(compare_Move(Add_best,best)==-1) {
                return Add_best;
            }else if(compare_Move(Add_best,best)==1){
                count_chose_exchang_in_small++;
                return best;
            }else{
                if(random.nextInt(2)==0)
                    return Add_best;
                else{
                    count_chose_exchang_in_small++;
                    return best;}
            }
        }
        Move Out_bestMv = new Move(null, null, Integer.MAX_VALUE, null);//用于记录<-a>的最好的结果；
        int  Out_best_count=0;
        find_cut_vertices();
        Move bestMv = new Move(null, null, Integer.MAX_VALUE, null);
        Move bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
        int best_count = 0;
        int best_count_t = 0;
        for(var moveOutV : X){
            //评估单移除
            if(moveOutV.is_cut)continue;
            if(moveOutV.tabu_iter>iter_count)continue;
            Move mv=evaluate_moveOut(moveOutV);
            int cmp= compare_Move(mv,Out_bestMv);
            if(cmp<0){
                Out_bestMv=mv;
                Out_best_count=1;
            }else if(cmp==0){
                Out_best_count++;
                if(random.nextInt(Out_best_count)==0){
                    Out_bestMv=mv;
                }
            }
            int delta_plus=mv.delta;
            for(var addInV : addInVs){
                if(is_infeasible_move(addInV, moveOutV)){
                    continue;
                }
                Move mvI= evaluate_move_exchange(addInV,moveOutV,delta_plus);
                if(addInV.tabu_iter<=iter_count){
                    int  cmpI=compare_Move(mvI, bestMv);
                    if(cmpI<0){
                        bestMv=mvI;
                        best_count=1;
                    }else if(cmpI==0){
                        best_count++;
                        if (random.nextInt(best_count) == 0) {
                            bestMv = mvI;//概率选择
                        }
                    }
                }else{
                    int cmpI = compare_Move(mvI, bestMv_t);
                    if(cmpI< 0){
                        bestMv_t = mvI;
                        best_count_t = 1;
                    }else if(cmpI == 0){
                        best_count_t ++;
                        if(random.nextInt(best_count_t)==0){
                            bestMv_t = mvI;
                        }
                    }
                }
            }
        }


        Move best = new Move(null, null, Integer.MAX_VALUE, null);//用于记录<-a,+b>的最好move;
        int cmpa = compare_Move(bestMv, bestMv_t);
        if(bestMv.addInV == null || cmpa > 0 && mv_improves_the_best(bestMv_t)){
            best = bestMv_t;
        }else {
            best = bestMv;
        }


        Move Add_bestMv = new Move(null, null, Integer.MAX_VALUE, null);
        Move Add_bestMv_t = new Move(null, null, Integer.MAX_VALUE, null);
        int Add_best_count = 0;
        int Add_best_count_t = 0;
        for(Vertex addInV:addInVs){
            Move mv = evaluate_moveAdd(addInV);
            if(addInV.tabu_iter<=iter_count){
                int cmp =compare_Move(mv, Add_bestMv);
                if(cmp < 0){
                    Add_bestMv = mv;
                    Add_best_count = 1;
                } else if (cmp == 0) {
                    Add_best_count++;
                    if (random.nextInt(Add_best_count) == 0) {
                        Add_bestMv = mv;//概率选择
                    }
                }
            } else{
                int cmp = compare_Move(mv, Add_bestMv_t);
                if(cmp < 0){
                    Add_bestMv_t = mv;
                    Add_best_count_t = 1;
                }else if(cmp == 0){
                    Add_best_count_t ++;
                    if(random.nextInt(Add_best_count_t)==0){
                        Add_bestMv_t = mv;
                    }
                }
            }
        }
        Move Add_best=null;
        cmpa=compare_Move(Add_bestMv,Add_bestMv_t);
        if(Add_bestMv.addInV==null||cmpa>0&&mv_improves_the_best(Add_bestMv_t)){
            Add_best = Add_bestMv_t;
        }else {
            Add_best = Add_bestMv;
        }
        int choice=choose_Last_Move(Out_bestMv,best,Add_best);
        if(choice==1){
            return Out_bestMv;
        }else if(choice==2){
            is_out=false;
            return best;
        }else {
            is_out=false;
            return Add_best;
        }

    }
    private boolean mv_improves_the_best(Move mv){
        if(currBestSol == null || currBestSol.not_dominated_count > 0 && mv.delta < 0){
            return true;
        }else if(currBestSol.not_dominated_count == 0
                && mv.tree != null
                && mv.tree.tree_weight < currBestSol.tree.tree_weight){
            return true;
        }else{
            return false;
        }
    }
    private int choose_Last_Move(Move a ,Move b,Move c){
        int cmp=compare_Move(a, b);
        int num=0;
        if(cmp<0){
            cmp=compare_Move(a,c);
            if(cmp<0){
                return 1;
            }else if(cmp==0){
                if(random.nextInt(2)==0){
                    return 1;
                }else return 3;
            }else return 3;
        }else if(cmp==0){
            num=random.nextInt(2)+1;
            if(num==1){
                cmp=compare_Move(a,c);
                if(cmp<0){
                    return 1;
                }else if(cmp==0){
                    if(random.nextInt(2)==0){
                        return 1;
                    }else return 3;
                }else return 3;
            }  else{
                cmp=compare_Move(b,c);
                if(cmp<0){
                    return 2;
                }else if(cmp==0){
                    if(random.nextInt(2)==0){
                        return 2;
                    }else return 3;
                }else return 3;

            }
        }else{ cmp=compare_Move(b,c);
            if(cmp<0){
                return 2;
            }else if(cmp==0){
                if(random.nextInt(2)==0){
                    return 2;
                }else return 3;
            }else return 3;

        }
    }
    private int compare_Move(Move a, Move b){
        if(a.delta == b.delta){
            return a.tree != null ? Double.compare(a.tree.tree_weight, b.tree.tree_weight) : 0;
        }else{
            return Integer.compare(a.delta, b.delta);
        }
    }
    private Move evaluate_moveAdd(Vertex addInV){//用于评估（+b）
        int delta=0;
        for(Edge e : graph.edge_list[addInV.index]){
            Vertex v = e.getOtherEdgeEnd(addInV);
            if(!v.is_in_X && v.degree_to_X == 0){
                delta--;
            }
        }
        SpanningTree new_tree=null;
        if(X_minu.size()+delta==0){
                var candidate_edges = collect_edges_in_X_after_moveAdd_Arry(addInV);
                new_tree = calc_spanning_tree(candidate_edges);

        }
        return new Move(addInV,null,delta,new_tree);
    }
    private Move evaluate_moveOut(Vertex moveOutV){//用于评估（-a）
        int delta=0;
        for(Edge e : graph.edge_list[moveOutV.index]){
            Vertex v = e.getOtherEdgeEnd(moveOutV);
            if(!v.is_in_X && v.degree_to_X == 1 ){
                delta++;
            }
        }
        SpanningTree new_tree=null;
        if(X_minu.size()+delta==0){
                var candidate_edges = collet_eges_in_X_after_moveOut_Arry(moveOutV);
                new_tree = calc_spanning_tree(candidate_edges);



        }
        return new Move(null,moveOutV,delta,new_tree);
    }
    private Move evaluate_move(Vertex addInV, Vertex moveOutV, boolean is_calc_tree){
        int delta = 0;
        for(Edge e : graph.edge_list[addInV.index]){
            Vertex v = e.getOtherEdgeEnd(addInV);
            if(!v.is_in_X && v.degree_to_X == 0){
                delta--;
            }
        }
        for(Edge e : graph.edge_list[moveOutV.index]){
            Vertex v = e.getOtherEdgeEnd(moveOutV);
            if(!v.is_in_X && v.degree_to_X == 1 && graph.get_edge_weight(v, addInV) == Double.MAX_VALUE){//最后一个条件是移入和移除相抵消；
                delta++;
            }
        }
        SpanningTree new_tree = null;

        if(is_calc_tree && X_minu.size() + delta == 0){

                var candidate_edges = collect_edges_in_X_after_move_Arr(addInV, moveOutV);
                new_tree = calc_spanning_tree(candidate_edges);
        }


        return new Move(addInV, moveOutV, delta, new_tree);
    }

    private Move evaluate_move_exchange(Vertex addInV, Vertex moveOutV, int delta_puls){
        int delta = delta_puls;
        for(Edge e : graph.edge_list[addInV.index]) {
            Vertex v = e.getOtherEdgeEnd(addInV);
            if (!v.is_in_X && v.degree_to_X == 0) {
                delta--;
            }
            if(!v.is_in_X && v.degree_to_X == 1 && graph.get_edge_weight(v,moveOutV) != Double.MAX_VALUE){
                delta--;
            }

        }
        SpanningTree new_tree = null;

        if( X_minu.size() + delta == 0){
                var candidate_edges = collect_edges_in_X_after_move_Arr(addInV, moveOutV);
                new_tree = calc_spanning_tree(candidate_edges);
        }


        return new Move(addInV, moveOutV, delta, new_tree);
    }


    private void make_move(Move mv){
        tree = mv.tree;
        if(mv.moveOutV!=null){
            remove_vertex_from_X(mv.moveOutV);
            if((int)(X_plus.size()*TTR)<=1){
                mv.moveOutV.tabu_iter = iter_count;
            }
            else mv.moveOutV.tabu_iter = iter_count + random.nextInt((int)(X_plus.size()*TTR));
        }
        if(mv.addInV!=null){
            add_vertex_to_X(mv.addInV);
            if((int)((X.size()-cut_count)*TTR)<=1){
                mv.addInV.tabu_iter = iter_count;
            }
            else mv.addInV.tabu_iter = iter_count +  random.nextInt((int)((X.size()-cut_count)*TTR));
        }
    }





    private int current_configuration_compare_sol(Solution sol){
        if(sol == null) return -1;
        int cmp = Integer.compare(X_minu.size(), sol.not_dominated_count);
        if(cmp == 0 && X_minu.size() == 0){
            cmp = Double.compare(tree.tree_weight, sol.tree.tree_weight);
        }
        return cmp;
    }

    private boolean find_any_feasible_tree(){

        currBestSol = new Solution(this);
        for(;;++iter_count){
            Move mv = find_move( false,get_reduced_candidate_insert_v());
            if(mv.delta >= 0 || X_minu.isEmpty()){
                break;
            }
            make_move(mv);

        }

        if(!X_minu.isEmpty()){
            return false;
        }

        tree = calc_spanning_tree(new ArrayList<>(collect_edges_set_in_X()));
//        tree.tree_sortedAllEdges=sortedAllEdges;
        currBestSol = new Solution(this);
        return true;
    }

    private ArrayList<Vertex> prepare_candidate_addIns(){
        if(X_minu.isEmpty()){
            return new ArrayList<>(X_plus);
        }else{
            return get_reduced_candidate_insert_v();
        }
    }

    private boolean local_search(){

        int X_size = get_best_solution_X_size();
        Solution solu = get_random_solution_in_pool(X_size);
        rebuilt_curr_sol(solu);
        currBestSol = solu;
        int fail_improve_count = 0;
        final int max_fail_count = MAX_FAIL_COUNT ;
        long log_time = System.currentTimeMillis();
        if(X_minu.isEmpty() && tree == null){
            throw new Error("local search error1");
        }
        int per_str_min = (int)(currBestSol.dominating_set.size() * PERTURB_STR_RATIO_MIN);
        int per_str_max = (int)(currBestSol.dominating_set.size() * PERTURB_STR_RATIO_MAX);
        for(;(System.currentTimeMillis() - start_time)/1000.0 < time_limit;++iter_count){
            ArrayList<Vertex> candidate_addIns = prepare_candidate_addIns();
            Move mv = find_move(candidate_addIns);
            make_move(mv);
            var solSet = solutionPools.get(X.size());
            if(solSet == null&&tree!=null){//扩大解池；
                solSet = new TreeSet<>();
                solSet.add(new Solution(this));
                solutionPools.put(X.size(), solSet);
                same_sol_again_count.put(X.size(), 0);
            }
            fail_improve_count++;
            if((mv.addInV==null)&&(mv.moveOutV==null)){

            }else {
                int cmp = current_configuration_compare_sol(currBestSol);//先比较x_minus 在比较weight，无需修改；
                if (cmp < 0) {
                    currBestSol = new Solution(this);
                    fail_improve_count = 0;
                    solSet = new TreeSet<>();
                    solSet.add(currBestSol);
                    solutionPools.put(X.size(), solSet);
                    same_sol_again_count.put(X.size(), 0);
                    best_x_size = X.size();
                    per_str_min = (int) (currBestSol.dominating_set.size() * PERTURB_STR_RATIO_MIN);
                    per_str_max = (int) (currBestSol.dominating_set.size() * PERTURB_STR_RATIO_MAX);

                } else if (cmp == 0) {
                    var currSol = new Solution(this);
                    if (solSet.contains(currSol)) {
                        if (mv.addInV != null || (last_add != null && !mv.moveOutV.equals(last_add))) {
                            same_sol_again_count.put(X.size(), same_sol_again_count.get(X.size()) + 1);
                        }

                    } else {
                        solSet.add(currSol);
                    }
                }
            }
            if(mv.moveOutV==null){
                last_add=mv.addInV;
            }else last_add=null;
            long curr_time = System.currentTimeMillis();
            if(curr_time - log_time > 5000) {
                System.out.print("\titer=" + iter_count + ", X_size=" + X.size());
                if (tree != null) {
                    System.out.println(", tree_w=" + String.format("%.2f", tree.tree_weight) + ", best_tree_w="+String.format("%.2f", currBestSol.tree.tree_weight));
                } else {
                    System.out.println(", X_m_size=" + X_minu.size());
                }
                log_time = curr_time;
            }
            if(fail_improve_count >= max_fail_count){
                Solution bestSol =currBestSol;
                int str =  Math.min(per_str_min + same_sol_again_count.get(best_x_size), per_str_max);
                perturb(str);
                per_count++;
                fail_improve_count =0;
            }

        }
        return X_minu.size() == 0;
    }

    private SpanningTree calc_spanning_tree(ArrayList<Edge> candidate_edges) {
        int[] disjoint_set = new int[graph.vertices.length];
        Arrays.fill(disjoint_set, -1);
        Collections.sort(candidate_edges);

        var tree_edges = new TreeSet<Edge>();
        var tree_weight = 0.0;

        tree_weight = kruskal_subprocess(candidate_edges, disjoint_set, tree_edges);

        return new SpanningTree(tree_edges, tree_weight);
    }





    private double kruskal_subprocess(ArrayList<Edge> candidate_edges, int[] disjoint_set, Set<Edge> tree_edges){
        var tree_weight = 0.0;
        for (var edge : candidate_edges) {
            int i = edge.source.index;
            while (disjoint_set[i] >= 0) i = disjoint_set[i];
            int j = edge.sink.index;
            while (disjoint_set[j] >= 0) j = disjoint_set[j];
            if (i != j) {
                tree_edges.add(edge);
                tree_weight += edge.weight;
                if (i < j) {
                    disjoint_set[i] += disjoint_set[j];
                    disjoint_set[j] = i;
                } else {
                    disjoint_set[j] += disjoint_set[i];
                    disjoint_set[i] = j;
                }
            }
        }
        return tree_weight;
    }

    private int depth;
    private int num_root_child;
    private Vertex root;

    private void find_cut_vertices() {
        cut_count=0;
        depth = 1;
        num_root_child = 0;
//        //System.out.println("在find_cut_vertices中x的个数"+X.size());
        for (Vertex v : X) {
            v.is_visited = false;
            v.dep = -1;
            v.low = -1;
            v.is_cut = false;
        }
        Vertex r = X.iterator().next();
        r.is_visited = true;
        root = r;
        cut_vertices_recur(r);
        if (num_root_child > 1) {
            r.is_cut = true;
            cut_count++;
        }
    }

    private void cut_vertices_recur(Vertex r) {
        r.is_visited = true;
        r.dep = depth;
        r.low = depth;
        ++depth;

        for (Edge e : graph.edge_list[r.index]) {
            Vertex tem = e.getOtherEdgeEnd(r);
            if (tem.is_in_X) {
                if (!tem.is_visited) {
                    cut_vertices_recur(tem);
                    r.low = Math.min(r.low, tem.low);
                    if (tem.low >= r.dep && r != root) {
                        r.is_cut = true;
                        cut_count++;
                    } else if (r == root) {
                        ++num_root_child;
                    }
                } else {
                    r.low = Math.min(r.low, tem.dep);
                }
            }
        }
    }

    private void check_split(){
        var check_set = new TreeSet<Vertex>();
        check_set.addAll(X);
        check_set.addAll(X_plus);
        check_set.addAll(X_minu);
        if(check_set.size() != graph.vertices.length){
            throw new Error("check split error 1!");
        }

        var X_cpy = new TreeSet<>(X);
        var X_plus_cpy = new TreeSet<>(X_plus);
        var X_minu_cpy = new TreeSet<>(X_minu);

        X_cpy.removeAll(X_plus_cpy);
        if(X_cpy.size() != X.size()){
            throw new Error("check split error 2!");
        }
        X_plus_cpy.removeAll(X_minu_cpy);
        if(X_plus_cpy.size() != X_plus.size()){
            throw new Error("check split error 3!");
        }
        X_minu_cpy.removeAll(X_cpy);
        if(X_minu_cpy.size() != X_minu.size()){
            throw new Error("check split error 4!");
        }
    }

    private void check_consistency(){
        for(Vertex v : graph.vertices){
            if(v.is_in_X ^ X.contains(v)){
                throw new Error("check consistency error 1, " + v.index);
            }
            int calc_degree_in_X = 0;
            for(Edge e : graph.edge_list[v.index]){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u.is_in_X){
                    calc_degree_in_X++;
                }
            }
            if(calc_degree_in_X != v.degree_to_X){
                throw new Error("check consistency error 2, " + v.index);
            }
            if((!v.is_in_X && v.degree_to_X > 0) ^ X_plus.contains(v)){
                throw new Error("check consistency error 3, " + v.index);
            }
            if((!v.is_in_X && v.degree_to_X == 0) ^ X_minu.contains(v)){
                throw new Error("check consistency error 4, " + v.index);
            }
        }
    }

    private void dfs_X_tree(Vertex parent, Vertex v, boolean[] visited){
        if(visited[v.index]){
            throw new Error("dfs_X_tree");
        }
        visited[v.index] = true;
        for(Edge e : graph.edge_list[v.index]){
            if(tree.tree_edges.contains(e)){
                Vertex u = e.getOtherEdgeEnd(v);
                if(u != parent) {
                    dfs_X_tree(v, u, visited);
                }
            }
        }
    }

    private void check_tree(){
        if(tree == null)return;
        for(Edge e : tree.tree_edges){
            if(!(X.contains(e.source) && X.contains(e.sink))){
                throw new Error("check tree error 1");
            }
        }
        if(tree.tree_edges.size() != X.size() - 1){
            var candidate = collect_edges_set_in_X();
            ArrayList<Edge>candidate_edges=new ArrayList<>(candidate);
            int[] disjoint_set = new int[graph.vertices.length];
            Arrays.fill(disjoint_set, -1);
            Collections.sort(candidate_edges);
            //System.out.println(candidate_edges);
            var tree_edges = new TreeSet<Edge>();
            var tree_weight = 0.0;
            tree_weight = kruskal_subprocess(candidate_edges, disjoint_set, tree_edges);
            //System.out.println("tree edge"+tree_edges);
            //System.out.println("x is"+X+"tree edges"+ tree.tree_edges);
            //System.out.println("tree.tree_edges.size"+ tree.tree_edges.size()+" X.size()"+X.size());
            throw new Error("check tree error 2");
        }
        boolean[] visited = new boolean[graph.vertices.length];
        dfs_X_tree(null, X.iterator().next(), visited);
    }

    void check_configuration(){
        check_split();
        check_consistency();
        check_tree();
    }



    static private class Move {
        final public Vertex addInV;
        final public Vertex moveOutV;
        final public int delta;
        final public SpanningTree tree;

        Move(Vertex addInV, Vertex moveOutV, int delta, SpanningTree tree) {
            this.addInV = addInV;
            this.moveOutV = moveOutV;
            this.delta = delta;
            this.tree = tree;
        }
    }
}
