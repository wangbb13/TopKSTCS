//
// Created by Luo on 2020/3/3.
//
#include "util.h"

/*
 * Cantor pairing function
 * */

bool debug_on = false;
bool debug_info = false;
bool debug_exp6 = false;

namespace ns {
    void from_json(const json &j, Config &c) {
        j.at("queryNode").get_to(c.query_node);
        j.at("deltaTruss").get_to(c.delta_truss);
        j.at("topk").get_to(c.topk);
    }
}

long long to_encode_edge(long long a, long long b, bool is_undirected) {
    a += 1, b += 1; // avoid the situation that the id of a node is zero
    if (INT64_MAX / a < b) {
        cerr << "Multiply overflow.\n";
        return -1;
    }

    if (is_undirected) {
        if (a > b) {
            std::swap(a, b);
        }
    }
    long long pi = (a + b) * (a + b + 1) / 2 + b;
    return pi;
}

long long to_encode_edge(const Edge *edge, bool is_undirected) {
    long long a = edge->node_a;
    long long b = edge->node_b;
    a += 1, b += 1; // avoid the situation that the id of a node is zero
    if (INT64_MAX / a < b) {
        cerr << "Multiply overflow.\n";
        return -1;
    }

    if (is_undirected) {
        if (a > b) {
            std::swap(a, b);
        }
    }
    long long pi = (a + b) * (a + b + 1) / 2 + b;
    return pi;
}

/*
 *  Inverting Cantor pairing function
 */
pair<long long, long long> to_decode_edge(long long val, bool is_undirected) {
    auto w = floor((sqrt(8 * val + 1) - 1) / 2);
    auto t = w * (w + 1) / 2;
    auto y = val - t;
    auto x = w - y;
    if (is_undirected) {
        if (y < x) {
            std::swap(x, y);
        }
    }
    return make_pair(x - 1, y - 1);
}


long long union_find(long long x, unordered_map<long long, long long> &c) {
    long long r = x;
    while (c[r] != r)
        r = c[r];
    long long i = x, j;
    while (i != r) {
        j = c[i];
        c[i] = r;
        i = j;
    }

    return r;
}

long long union_find(long long x, vector<long long> &c) {
    long long r = x;
    while (c[r] != r)
        r = c[r];
    long long i = x, j;
    while (i != r) {
        j = c[i];
        c[i] = r;
        i = j;
    }

    return r;
}

void union_join(long long x, long long y, unordered_map<long long, long long> &c) {
    long long rx = union_find(x, c);
    long long ry = union_find(y, c);
    if (rx != ry)
        c[rx] = ry;
}

void union_join(long long x, long long y, vector<long long> &c) {
    long long rx = union_find(x, c);
    long long ry = union_find(y, c);
    if (rx != ry)
        c[rx] = ry;
}


void
equiTruss_community_search(const SuperGraph &superGraph, const unordered_map<long long, unordered_set<long long>> &H,
                           const Truss &truss, long long k, long long query_node, Communities *&__communities) {
    /* Initialization */
    unordered_map<long long, bool> processed;
    unordered_set<long long> nodes;
    unordered_map<long long, SuperNode *> id2node;

    for (const auto &_ : superGraph)
        nodes.insert(_.first->super_id);
    for (const auto &v: nodes)
        processed[v] = false;
    for (const auto &_: superGraph)
        id2node[_.first->super_id] = _.first;
    long long l = 0;
    /* BFS traversal for community search */
    assert(H.find(query_node) != H.end());
    for (const auto &v : H.at(query_node)) {
        if (id2node.at(v)->truss >= k && !processed.at(v)) {
            processed[v] = true;
            l += 1;

            deque<long long> Q;
            Q.push_back(v);
            Graph A;
            while (!Q.empty()) {
                long long v_ = Q.front();
                Q.pop_front();

                merge_graph(A, id2node[v_]->edges);
                assert(superGraph.find(id2node[v_]) != superGraph.end());
                for (const auto &sn: superGraph.at(id2node[v_])) {
                    if (sn->truss >= k && !processed.at(sn->super_id)) {
                        processed[sn->super_id] = true;
                        Q.push_back(sn->super_id);
                    }
                }
            }
            __communities->push_back(A);
        }
    }
}


unordered_map<long long, unordered_set<long long>>
equiTruss_index_contruction(const Graph &projected_graph, const Truss &truss, const HashedEdge &temporal_edge_hash,
                            long long max_truss, SuperGraph &__superGraph) {
    /* Initialization */
    unordered_map<long long, bool> edge_processed;
    unordered_map<long long, unordered_set<long long>> edge_list;
    unordered_map<long long, deque<long long>> phi;
    unordered_map<long long, unordered_set<long long>> H;
    for (const auto &e: temporal_edge_hash) {
        edge_processed[e] = false;
        unordered_set<long long> _;
        edge_list[e] = _;   // empty set
        assert(truss.find(e) != truss.end());   // make sure algorithm runs correctly
        phi[truss.at(e)].push_back(e);
    }
    long long snID = 0;
    deque<long long> Q;
    /* Index Construction */
    unordered_map<long long, SuperNode *> id2node;
    unordered_set<long long> V;
    for (long long k = 3; k < max_truss + 1; ++k) {
        if (phi.find(k) == phi.end())
            continue;
        deque<long long> &phi_ref_k = phi.at(k); // ref
        while (!phi_ref_k.empty()) {
            long long e = phi_ref_k.front();
//            phi_ref_k.pop_front();

            assert(edge_processed.find(e) != edge_processed.end());
            edge_processed[e] = true;
            auto *sn = new SuperNode(++snID);
            sn->truss = k; // record trusness
            V.insert(snID);
            unordered_set<SuperNode *> _;
            __superGraph[sn] = _;
            id2node[snID] = sn;
            Q.push_back(e);
            while (!Q.empty()) {
                long long q_e = Q.front();
                pair<long long, long long> edge = to_decode_edge(q_e);
                Q.pop_front();

                sn->edges[edge.first].insert(edge.second);
                sn->edges[edge.second].insert(edge.first);
                // Hash structure
                H[edge.first].insert(snID);
                H[edge.second].insert(snID);
                assert(edge_list.find(q_e) != edge_list.end());
                for (const auto &id: edge_list.at(q_e)) {
                    if (V.find(id) != V.end()) {
                        assert(id2node.find(id) != id2node.end());
                        __superGraph[sn].insert(id2node[id]);
                        __superGraph[id2node[id]].insert(sn);
                    }
                }
                unordered_set<long long> one_have;
                for (const auto &_: projected_graph.at(edge.first))
                    one_have.insert(_);
                for (const auto &_ : projected_graph.at(edge.second)) {
                    if (one_have.find(_) != one_have.end()) {
                        if (truss.at(to_encode_edge(edge.first, _)) >= k &&
                            truss.at(to_encode_edge(edge.second, _)) >= k) {
                            processEdge(edge.first, _, truss, k, snID, edge_processed, Q, edge_list);
                            processEdge(edge.second, _, truss, k, snID, edge_processed, Q, edge_list);
                        }
                    }
                }
                long long offset = 0;
                for (const auto &e_k: phi_ref_k) {
                    if (e_k == q_e) {
                        break;
                    } else offset++;
                }
                phi_ref_k.erase(phi_ref_k.begin() + offset);
            }
        }
    }
    return H;
}


Branch tcp_index_construction(const Graph &graph, Truss &graph_truss, TCPIndex &__tx) {
    Branch brach;
    for (const auto &x: graph) {
        unordered_map<long long, long long> edge_weight;
        vector<long long> neighbors;
        long long kmax = INT32_MIN;
        unordered_map<long long, long long> marks;  // connected component id
        for (const auto &n: graph)
            marks[n.first] = 0;
        for (const auto &i: graph)
            marks[i.first] = i.first;

        for (const auto &n: graph.at(x.first))
            neighbors.push_back(n);
        for (long long y = 0; y < neighbors.size(); y++) {
            for (long long z = y + 1; z < neighbors.size(); z++) {
                if (graph.at(neighbors[y]).find(neighbors[z]) != graph.at(neighbors[y]).end()) {
                    vector<long long> _;
                    _.push_back(graph_truss[to_encode_edge(neighbors[y], neighbors[z])]);
                    _.push_back(graph_truss[to_encode_edge(x.first, neighbors[z])]);
                    _.push_back(graph_truss[to_encode_edge(x.first, neighbors[y])]);
                    auto min_val = *min_element(begin(_), end(_));
                    edge_weight[to_encode_edge(neighbors[y], neighbors[z])] = min_val;
                    if (min_val > kmax) kmax = min_val;
                }
            }
        }
        unordered_map<long long, unordered_map<long long, long long>> tx_gneighbor;
        for (const auto &n: neighbors) {
            unordered_map<long long, long long> epty;
            tx_gneighbor[n] = epty;
        }
        __tx[x.first] = tx_gneighbor;

        unordered_set<long long> current_added_nodes;   // calculate #braches
        long long num_of_different_component_edges = 0;

        for (long long k = kmax; k >= 2; k--) {
            for (const auto &edge: edge_weight) {
                if (edge.second == k) {
                    pair<long long, long long> code = to_decode_edge(edge.first);
                    long long y = code.first, z = code.second;
                    current_added_nodes.insert(y);
                    current_added_nodes.insert(z);
                    if (union_find(y, marks) != union_find(z, marks)) {
                        __tx[x.first][y][z] = k;
                        __tx[x.first][z][y] = k;
                        union_join(z, y, marks);
                        num_of_different_component_edges += 1;  // add one.
                    }
                }
            }
            assert(current_added_nodes.size() > num_of_different_component_edges);
            brach[x.first][k] = current_added_nodes.size() - num_of_different_component_edges;
        }

    }
    return brach;
}

void dfs_visit(const Graph &g, Nodes &visited, long long node) {
    for (const auto &n: g.at(node)) {
        if (visited.find(n) != visited.end())
            continue;

        dfs_visit(g, visited, n);
    }
    visited.insert(node);
}


long long truss_decomposition(Graph &graph, Truss &__truss) {
    long long k = 1;
    // calculate all sups in graph G.
    unordered_map<long long, long long> sup;
    long long max_truss = 0;
    // initialize the support
    for (const auto &u: graph)
        for (const auto &v: graph.at(u.first))
            sup[to_encode_edge(u.first, v)] = 0;

    for (const auto &u: graph) {
        for (const auto &v : graph.at(u.first)) {
            long long edge_val = to_encode_edge(u.first, v);
            if (sup.find(edge_val) != sup.end() && sup[edge_val] == 0) { // undirected graph
                for (const auto &w: graph) {
                    // find a triangle wrt edge e(u, v)
                    if (graph.at(w.first).find(u.first) != graph.at(w.first).end() &&
                        graph.at(w.first).find(v) != graph.at(w.first).end() &&
                        w.first != u.first && w.first != v) { // u, v, w consist a triangle
                        sup[edge_val]++;
                    }
                }
            }
        }
    }

    long long edge_num = sup.size();
    vector<long long> del_code;
    while (edge_num > 0) {
        k++;
        deque<long long> queue;
        for (const auto &s: sup)
            if (s.second <= k - 2)
                queue.push_back(s.first);
        while (!queue.empty()) {
            std::sort(begin(queue), end(queue));
            long long code = queue.front();
            queue.pop_front();

            pair<long long, long long> edge = to_decode_edge(code);
            long long u = edge.first, v = edge.second;
            for (const auto &w: graph[u]) {
                if (graph[w].find(v) == graph[w].end())
                    continue;
                --sup[to_encode_edge(u, w)];
                --sup[to_encode_edge(v, w)];
                if (sup[to_encode_edge(u, w)] == k - 2)
                    queue.push_back(to_encode_edge(u, w));
                if (sup[to_encode_edge(v, w)] == k - 2)
                    queue.push_back(to_encode_edge(v, w));
            }
            if (k > max_truss) max_truss = k;
            __truss[code] = k;
            sup.erase(code);
            graph[u].erase(v);
            graph[v].erase(u);
            --edge_num;

            del_code.push_back(code);
        }
    }
    // restore the graph.
    for (const auto &code: del_code) {
        auto p = to_decode_edge(code);
        long long u = p.first, v = p.second;
        graph[u].insert(v);
        graph[v].insert(u);
    }
    return max_truss;
}

long long truss_decomposition(Graphs &g, Truss &__truss) {
    long long k = 1;
    unordered_map<long long, long long> sup;
    long long max_truss = 0;
    for (const auto &edge: g.edges) {
        sup[to_encode_edge(edge->node_a, edge->node_b)] = 0;
    }
    for (const auto &node: g.nodes) {
        for (const auto &edge: node->connTo) {
            if (edge->node_a == edge->node_b) continue;
            long long edge_code = to_encode_edge(edge->node_a, edge->node_b);
            if (sup.find(edge_code) != sup.end() && sup.at(edge_code) == 0) {
                for (const auto &node_id: neighbors(g, edge_code)) {
                    sup[edge_code]++;
                }
            }
        }
    }
    long long edge_num = sup.size();
    while (edge_num > 0) {
        k++;
        deque<long long> queue;
        for (const auto &s :sup) {
            if (s.second <= k - 2) {
                queue.push_back(s.first);
            }
        }
        while (!queue.empty()) {
            std::sort(begin(queue), end(queue));
            long long hashcode = queue.front();
            queue.pop_front();

            pair<long long, long long> edge = to_decode_edge(hashcode);
            long long u = edge.first, v = edge.second;

            for (const auto &w: neighbors(g, hashcode)) {
                --sup[to_encode_edge(w, u)];
                --sup[to_encode_edge(w, v)];
                if (sup[to_encode_edge(u, w)] == k - 2) {
                    queue.push_back(to_encode_edge(u, w));
                }
                if (sup[to_encode_edge(v, w)] == k - 2) {
                    queue.push_back(to_encode_edge(v, w));
                }
            }
            if (k > max_truss) max_truss = k;
            __truss[hashcode] = k;
            sup.erase(hashcode);
            --edge_num;


            g.id2node.at(u)->connTo.erase(remove(g.id2node.at(u)->connTo.begin(), g.id2node.at(u)->connTo.end(),
                                                 g.hashedEdge.at(to_encode_edge(u, v))));
            g.id2node.at(v)->connTo.erase(remove(g.id2node.at(v)->connTo.begin(), g.id2node.at(v)->connTo.end(),
                                                 g.hashedEdge.at(to_encode_edge(u, v))));
            g.hashedEdge.erase(to_encode_edge(u, v));
        }
    }
    // restore
    for (const auto &edge: g.edges) {
        if (g.hashedEdge.find(to_encode_edge(edge->node_b, edge->node_a)) == g.hashedEdge.end()) {
            g.hashedEdge.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
            g.id2node.at(edge->node_a)->connTo.push_back(edge);
            g.id2node.at(edge->node_b)->connTo.push_back(edge);
        }
    }

    return max_truss;
}

void load_temporal_networks(const string &filename, Graphs &__graphs, long long &last_timestamp) {
    ifstream fin(filename);
    if (!fin.is_open()) {
        char buff[255];
        getcwd(buff, sizeof(buff));
        cerr << "File Not Open, current in" << buff << ".\n";
        exit(0xff);
    }
    string datum;
    while (getline(fin, datum)) {
        long long from, to, temporal;
        stringstream ss(datum);
        ss >> from >> to >> temporal;

        if (from == to) continue;   // 不接受自环

        Node *node1 = __graphs.newNode(from);
        Node *node2 = __graphs.newNode(to);
        Edge *edge = __graphs.newEdge(from, to, temporal);

        // Edge process
        last_timestamp = last_timestamp < temporal ? temporal : last_timestamp;
    }

    FILE *fp = stderr;
    fprintf(fp, "Loading completed, with nodes %lu ,edges %lu\n", __graphs.nodes.size(),
            __graphs.edges.size());
}

void load_temporal_networks(const string &filename, Nodes &g_nodes, HashedEdge &g_hashedEdge, Graph &g_graph,
                            TemporalGraph &g_temporal_graph, long long &last_timestamp) {
    ifstream fin(filename);
    if (!fin.is_open()) {
        char buff[255];
        getcwd(buff, sizeof(buff));
        cerr << "File Not Open, current in" << buff << ".\n";
        exit(0xff);
    }
    string datum;
    while (getline(fin, datum)) {
        long long from, to, temporal;
        stringstream ss(datum);
        ss >> from >> to >> temporal;

        g_nodes.insert(from);
        g_nodes.insert(to);

        g_graph[from].insert(to);   // static graph
        g_graph[to].insert(from);   // static graph

        g_hashedEdge.insert(to_encode_edge(from, to)); // hashed graph edge

        g_temporal_graph[temporal][from].insert(to); // temporal graph
        g_temporal_graph[temporal][to].insert(from); // temporal graph

        last_timestamp = last_timestamp < temporal ? temporal : last_timestamp;
    }

    FILE *fp = stderr;
    fprintf(fp, "Loading completed, with nodes %lu ,edges %lu ,temporal edges %lld\n", g_nodes.size(),
            g_hashedEdge.size(), cal_temporal_edges(g_temporal_graph));
}

void
processEdge(long long u, long long v, const Truss &truss, const long long k, const long long snId,
            unordered_map<long long, bool> &processed, deque<long long> &Q,
            unordered_map<long long, unordered_set<long long>> &edge_list) {
    long long e = to_encode_edge(u, v);
    if (truss.at(e) == k) {
        if (!processed.at(e)) {
            processed[e] = true;
            Q.push_back(e);
        }
    } else {
        assert(edge_list.find(e) != edge_list.end());
        if (edge_list[e].find(snId) == edge_list[e].end()) {
            edge_list[e].insert(snId);
        }
    }
}

void
merge_graph(Graph &g, const unordered_map<long long, unordered_set<long long>> &edges) {
    for (const auto &edge: edges) {
        for (const auto &n: edge.second) {
            g[edge.first].insert(n);
            g[n].insert(edge.first);
        }
    }
}


long long cal_temporal_edges(const TemporalGraph &g_temporal_graph) {
    long long sum = 0;
    for (const auto &graph : g_temporal_graph)
        for (const auto &g: graph.second)
            sum += g.second.size();
    return sum;
}

vector<Graphs> baseline_community_detection_with_truss(Graphs g, const Truss &truss, const long long k) {
    unordered_map<long long, bool> visited;
    vector<Graphs> communities;
    for (const auto &edge: g.edges) {
        visited[to_encode_edge(edge->node_a, edge->node_b)] = false;
    }

    for (const auto &node: g.nodes) {
        for (const auto &edge : node->connTo) {
            long long u = edge->node_a == node->node_id ? edge->node_b : edge->node_a;
            if (truss.at(to_encode_edge(node->node_id, u)) >= k &&
                !visited.at(to_encode_edge(node->node_id, u))) {
                deque<long long> queue;
                queue.push_back(to_encode_edge(node->node_id, u));
                visited[to_encode_edge(node->node_id, u)] = true;
                Graphs c;
                while (!queue.empty()) {
                    long long hashcode = queue.front();
                    queue.pop_front();
                    pair<long long, long long> pop_edge = to_decode_edge(hashcode);
                    long long x = pop_edge.first, y = pop_edge.second;
                    c.newEdgeFrom(g.hashedEdge.at(hashcode));
                    for (const auto &neighbor: g.nodes) {
                        if (neighbor->node_id != x && neighbor->node_id != y &&
                            g.hashedEdge.find(to_encode_edge(neighbor->node_id, x)) != g.hashedEdge.end() &&
                            g.hashedEdge.find(to_encode_edge(neighbor->node_id, y)) != g.hashedEdge.end()) {
                            if (truss.at(to_encode_edge(neighbor->node_id, x)) >= k &&
                                truss.at(to_encode_edge(neighbor->node_id, y)) >= k) {
                                if (!visited.at(to_encode_edge(neighbor->node_id, x))) {
                                    queue.push_back(to_encode_edge(neighbor->node_id, x));
                                    visited[to_encode_edge(neighbor->node_id, x)] = true;
                                }
                                if (!visited.at(to_encode_edge(neighbor->node_id, y))) {
                                    queue.push_back(to_encode_edge(neighbor->node_id, y));
                                    visited[to_encode_edge(neighbor->node_id, y)] = true;
                                }
                            }  //endif
                        } //endfor
                    }
                } //endwhile
                communities.push_back(c);
            } //endif
        }
    } // endfor

    return communities;
}


vector<Graphs>
baseline_community_search_with_truss(Graphs g, const Truss &truss, const long long k, const long long vq) {
    unordered_map<long long, bool> visited;
    vector<Graphs> communities;
    for (const auto &edge: g.edges) {
        visited[to_encode_edge(edge->node_a, edge->node_b)] = false;
    }
    assert(g.id2node.find(vq) != g.id2node.end());
    for (const auto &edge : g.id2node.at(vq)->connTo) {
        long long u = edge->node_a == vq ? edge->node_b : edge->node_a;
        if (truss.at(to_encode_edge(vq, u)) >= k &&
            !visited.at(to_encode_edge(vq, u))) {
            deque<long long> queue;
            queue.push_back(to_encode_edge(vq, u));
            visited[to_encode_edge(vq, u)] = true;
            Graphs c;
            while (!queue.empty()) {
                long long hashcode = queue.front();
                queue.pop_front();
                pair<long long, long long> pop_edge = to_decode_edge(hashcode);
                long long x = pop_edge.first, y = pop_edge.second;
                c.newEdgeFrom(g.hashedEdge.at(hashcode));
                for (const auto &neighbor: neighbors(g, to_encode_edge(x, y))) {
                    if (truss.at(to_encode_edge(neighbor, x)) >= k &&
                        truss.at(to_encode_edge(neighbor, y)) >= k) {
                        if (!visited.at(to_encode_edge(neighbor, x))) {
                            queue.push_back(to_encode_edge(neighbor, x));
                            visited[to_encode_edge(neighbor, x)] = true;
                        }
                        if (!visited.at(to_encode_edge(neighbor, y))) {
                            queue.push_back(to_encode_edge(neighbor, y));
                            visited[to_encode_edge(neighbor, y)] = true;
                        }
                    } //endfor
                }
            } //endwhile
            communities.push_back(c);
        } //endif
    }

    return communities;
}

vector<vector<long long>> enumNodes(const vector<long long> &nodes, const long long k) {
    vector<vector<long long>> __vec;
    vector<long long> ans;
    __enumNodes(nodes, k, ans, 0, __vec);
    return __vec;
}

void __enumNodes(const vector<long long> &nodes, const long long k, vector<long long> &ans, long long counter,
                 vector<vector<long long>> &__vec) {
    if (ans.size() == k) {
        __vec.push_back(ans);
        ans.erase(ans.begin() + ans.size() - 1);
        return;
    }

    for (counter; counter < SIZE(nodes); counter++) {
        ans.push_back(nodes[counter]);
        __enumNodes(nodes, k, ans, counter + 1, __vec);
    }
    ans.erase(ans.begin() + ans.size() - 1);
}

vector<vector<pair<long long, long long>>> enmuMTCCPeriod(const Graphs &g, const long long topk) {
    assert(g.edges.size() > 2);
    Edge *edge = g.edges.at(0);
    vector<vector<pair<long long, long long>>> container;
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) init_intervals.emplace_back(oc);

    for (int _i = 1; _i < SIZE(g.edges); ++_i) {
        Edge *cur_edge = g.edges.at(_i);
        vector<long long> vals;
        if (_i == 1) {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ei = 0; _ei < SIZE(init_intervals); ++_ei) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); ++_ej) {
                    vals.emplace_back(abs(init_intervals.at(_ei) - cur_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ej + _ei * SIZE(cur_edge->occur),
                                              make_pair(init_intervals.at(_ei), cur_edge->occur.at(_ej))));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            long long minInterval = vals.at(idx.at(0));
            long long _curTopk = 0;
            for (int _idx = 0; _idx < SIZE(idx); ++_idx) {
                if (vals.at(idx.at(_idx)) > minInterval) {
                    minInterval = vals.at(idx.at(_idx));
                    ++_curTopk;
                }
                if (_curTopk >= topk) break;
                vector<pair<long long, long long>> span(2, pair<long long, long long>(0, INT32_MAX));
                pair<long long, long long> intervals = id2edges.at(idx.at(_idx));
                // 0: Min, 1: Max
                span[0].second = std::min(intervals.first, intervals.second);
                span[1].second = std::max(intervals.first, intervals.second);
                span.emplace_back(to_encode_edge(edge->node_a, edge->node_b), intervals.first);
                span.emplace_back(to_encode_edge(cur_edge->node_a, cur_edge->node_b), intervals.second);
                assert(span[1].second - span[0].second == minInterval);
                container.push_back(span);
            }
        } else {
            unordered_map<long long, long long> id2period;
            for (long long _ek = 0; _ek < SIZE(container); _ek++) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); _ej++) {
                    if (container[_ek][0].second <= cur_edge->occur.at(_ej) &&
                        container[_ek][1].second >= cur_edge->occur.at(_ej)) {
                        vals.push_back(abs(container[_ek][0].second - container[_ek][1].second));
                    } else {
                        vals.push_back(abs(container[_ek][0].second - cur_edge->occur.at(_ej)) >
                                       abs(container[_ek][1].second - cur_edge->occur.at(_ej)) ?
                                       abs(container[_ek][0].second - cur_edge->occur.at(_ej)) : abs(
                                        container[_ek][1].second - cur_edge->occur.at(_ej)));
                    }
                    id2period.insert(make_pair(_ek * cur_edge->occur.size() + _ej, cur_edge->occur.at(_ej)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            vector<vector<pair<long long, long long>>> _c;
            long long minInterval = vals.at(idx.at(0));
            long long _curTopk = 0;
            for (unsigned long _idx : idx) {
                if (vals.at(_idx) > minInterval) {
                    minInterval = vals.at(_idx);
                    ++_curTopk;
                }
                if (_curTopk >= topk) break;
                assert(id2period.find(_idx) != id2period.end());
                long long interval = id2period.at(_idx);
                long long slot = _idx / SIZE(cur_edge->occur);
                vector<pair<long long, long long>> _span;
                _span.assign(begin(container[slot]), end(container[slot]));
                _span.emplace_back(make_pair(to_encode_edge(cur_edge->node_b, cur_edge->node_a), interval));
                if (_span[0].second > interval) _span[0].second = interval;
                if (_span[1].second < interval) _span[1].second = interval;

                _c.emplace_back(_span);
            }

            // update top-k storage
            container.clear();
            for (const auto &_: _c) {
                container.emplace_back(_);
            }
        } // end else
    }

    return container;
}

vector<pair<long long, long long>> enmuTopkTCCPeriodEqual(const Graphs &g) {
    assert(g.edges.size() > 1);
    Edge *edge = g.edges.at(0);
    vector<pair<long long, long long>> minimalPairs;
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) init_intervals.emplace_back(oc);

    for (int _i = 1; _i < SIZE(g.edges); ++_i) {
        Edge *cur_edge = g.edges.at(_i);
        vector<long long> vals;
        if (_i == 1) {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ei = 0; _ei < SIZE(init_intervals); ++_ei) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); ++_ej) {
                    auto minVal = std::min(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    auto maxVal = std::max(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    vals.emplace_back(abs(init_intervals.at(_ei) - cur_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ej + _ei * SIZE(cur_edge->occur),
                                              make_pair(minVal, maxVal)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            auto minp = id2edges.at(idx.at(0));
            long long interval = minp.second - minp.first;
            for (const auto &_dx: idx) {
                auto _inter = id2edges.at(_dx);
                if (_inter.second - _inter.first == interval) {
                    if (std::find(begin(minimalPairs), end(minimalPairs), _inter) == end(minimalPairs)) {
                        minimalPairs.emplace_back(_inter);
                    }
                } else break;
            }
//            minimalPair = id2edges.at(idx.at(0)); // 0: min, 1: max
        } else {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ej = 0; _ej < SIZE(cur_edge->occur); _ej++) {
                auto oc = cur_edge->occur.at(_ej);
                for (long long _ek = 0; _ek < SIZE(minimalPairs); _ek++) {
                    auto minp = minimalPairs.at(_ek);
                    if (oc <= minp.second && oc >= minp.first) {
                        vals.emplace_back(abs(minp.second - minp.first));
                        id2edges.insert(make_pair(_ej * SIZE(minimalPairs) + _ek, make_pair(minp.first, minp.second)));
                    } else {
                        vals.emplace_back(std::max(abs(oc - minp.first), abs(oc - minp.second)));
                        auto maxVal = std::max(oc, minp.second);
                        auto minVal = std::min(oc, minp.first);
                        id2edges.insert(make_pair(_ej * SIZE(minimalPairs) + _ek, make_pair(minVal, maxVal)));
                    }

                }
            }
            // 清空历史记录
            minimalPairs.clear();

            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            auto minp = id2edges.at(idx.at(0));
            long long interval = minp.second - minp.first;
            for (const auto &_dx: idx) {
                auto _inter = id2edges.at(_dx);
                if (_inter.second - _inter.first == interval) {
                    if (std::find(begin(minimalPairs), end(minimalPairs), _inter) == end(minimalPairs)) {
                        minimalPairs.emplace_back(_inter);
                    }
                } else break;
            }
        } // end else
    }

    return minimalPairs;
}

pair<long long, long long> enmuTopkTCCPeriodByOne(const Graphs &g) {
    assert(g.edges.size() > 1);
    Edge *edge = g.edges.at(0);
    pair<long long, long long> minimalPair;
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) init_intervals.emplace_back(oc);

    for (int _i = 1; _i < SIZE(g.edges); ++_i) {
        Edge *cur_edge = g.edges.at(_i);
        vector<long long> vals;
        if (_i == 1) {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ei = 0; _ei < SIZE(init_intervals); ++_ei) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); ++_ej) {
                    auto minVal = std::min(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    auto maxVal = std::max(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    vals.emplace_back(abs(init_intervals.at(_ei) - cur_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ej + _ei * SIZE(cur_edge->occur),
                                              make_pair(minVal, maxVal)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            minimalPair = id2edges.at(idx.at(0)); // 0: min, 1: max
        } else {
            unordered_map<long long, long long> id2edges;
            for (long long _ej = 0; _ej < SIZE(cur_edge->occur); _ej++) {
                auto oc = cur_edge->occur.at(_ej);
                if (oc <= minimalPair.second && oc >= minimalPair.first) {
                    vals.emplace_back(abs(minimalPair.second - minimalPair.first));
                } else {
                    vals.emplace_back(std::max(abs(oc - minimalPair.first), abs(oc - minimalPair.second)));
                }
                id2edges.insert(make_pair(_ej, oc));
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            long long curVal = id2edges.at(idx.at(0));
            minimalPair.first = std::min(minimalPair.first, curVal);
            minimalPair.second = std::max(minimalPair.second, curVal);
        } // end else
    }

    return minimalPair;
}


vector<vector<pair<long long, long long>>> enmuPeriod(const Graphs &g, const long long topk) {
    assert(g.edges.size() > 2);
    Edge *edge = g.edges.at(0);
    vector<vector<pair<long long, long long>>> spans;
    // 0: Min, 1: Max
    spans.assign(topk, vector<pair<long long, long long>>(2, pair<long long, long long>(0, INT32_MAX)));
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) {
        init_intervals.push_back(oc);
    }

    for (int i = 1; i < g.edges.size(); i++) {
        Edge *com_edge = g.edges.at(i);
        vector<long long> vals;
        if (i == 1) {
            // 根据索引分枝定界，取topk
            unordered_map<long long, pair<long long, long long>> id2edges;
            unordered_map<long long, long long> id2Min;
            unordered_map<long long, long long> id2Max;
            for (long long _ei = 0; _ei < init_intervals.size(); _ei++) {
                for (long long _ej = 0; _ej < com_edge->occur.size(); _ej++) {
                    vals.push_back(abs(init_intervals.at(_ei) - com_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ei * com_edge->occur.size() + _ej,
                                              make_pair(init_intervals.at(_ei), com_edge->occur.at(_ej))));
                    long long minVal = init_intervals.at(_ei) <= com_edge->occur.at(_ej) ? init_intervals.at(_ei)
                                                                                         : com_edge->occur.at(_ej);
                    long long maxVal = init_intervals.at(_ei) > com_edge->occur.at(_ej) ? init_intervals.at(_ei)
                                                                                        : com_edge->occur.at(_ej);
                    id2Min.insert(make_pair(_ei * com_edge->occur.size() + _ej, minVal));
                    id2Max.insert(make_pair(_ei * com_edge->occur.size() + _ej, maxVal));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            for (int k = 0; k < topk && k < idx.size(); k++) {
                assert(id2edges.find(idx.at(k)) != id2edges.end());
                auto intervals = id2edges.at(idx.at(k));
                spans[k].push_back(make_pair(to_encode_edge(edge->node_b, edge->node_a), intervals.first));
                spans[k].push_back(make_pair(to_encode_edge(com_edge->node_a, com_edge->node_b), intervals.second));
                spans[k][0].second = id2Min.at(idx.at(k));
                spans[k][1].second = id2Max.at(idx.at(k));
            }
        } else {
            unordered_map<long long, long long> id2period;
            for (long long _ek = 0; _ek < topk; _ek++) {
                if (spans[_ek][0].second == INT32_MAX) continue; // topk not reachable
                for (long long _ej = 0; _ej < com_edge->occur.size(); _ej++) {
                    if (spans[_ek][0].second <= com_edge->occur.at(_ej) &&
                        spans[_ek][1].second >= com_edge->occur.at(_ej)) {
                        vals.push_back(abs(spans[_ek][0].second - spans[_ek][1].second));
                    } else {
                        vals.push_back(abs(spans[_ek][0].second - com_edge->occur.at(_ej)) >
                                       abs(spans[_ek][1].second - com_edge->occur.at(_ej)) ?
                                       abs(spans[_ek][0].second - com_edge->occur.at(_ej)) : abs(
                                        spans[_ek][1].second - com_edge->occur.at(_ej)));
                    }
                    id2period.insert(make_pair(_ek * com_edge->occur.size() + _ej, com_edge->occur.at(_ej)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);

            for (int k = 0; k < topk && k < idx.size(); k++) {
                assert(id2period.find(idx.at(k)) != id2period.end());
                long long interval = id2period.at(idx.at(k));
                if (spans[k][0].second == INT32_MAX) {
                    // copy from above
                    long long slot = idx.at(k) / com_edge->occur.size();
                    spans[k].assign(begin(spans[slot]), end(spans[slot]));
                }
                spans[k].push_back(make_pair(to_encode_edge(com_edge->node_b, com_edge->node_a), interval));
                if (spans[k][0].second > interval) spans[k][0].second = interval;
                if (spans[k][1].second < interval) spans[k][1].second = interval;
            }
        }
    } // end forloop for edges.

    return spans;
}

template<typename T>
vector<size_t> sort_indexes(const vector<T> &v) {
    vector<size_t> idx(v.size());
    std::iota(idx.begin(), idx.end(), 0);

    std::sort(idx.begin(), idx.end(), [&](size_t i, size_t j) -> bool {
        return v[i] < v[j];
    });

    return idx;
}


vector<vector<pair<long long, long long>>>
updatePeriod(const Graphs &g, const Graphs &newG, const vector<vector<pair<long long, long long>>> &spans) {
    unordered_map<long long, Edge *> edges;
    unordered_map<long long, Edge *> newRestEdges;
    vector<vector<pair<long long, long long>>> expandSpans;
    expandSpans.assign(begin(spans), end(spans));
    for (const auto &edge: g.edges) {
        edges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
    }
    for (const auto &edge: newG.edges) {
        if (edges.find(to_encode_edge(edge->node_a, edge->node_b)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }
    }

    for (const auto &edge: newRestEdges) {
        Edge *rest = edge.second;
        vector<long long> vals;
        unordered_map<long long, long long> id2period;
        for (long long _ei = 0; _ei < SIZE(spans); _ei++) {
            auto span = spans.at(_ei);
            for (long long _ej = 0; _ej < rest->occur.size(); _ej++) {
                long long oc = rest->occur.at(_ej);
                if (oc >= span[0].second || oc <= span[1].second) {
                    vals.push_back(abs(span[0].second - span[1].second));
                } else {
                    vals.push_back(abs(span[0].second - oc) > abs(span[1].second - oc) ?
                                   abs(span[0].second - oc) : abs(span[1].second - oc));
                }
                id2period.insert(make_pair(_ei * rest->occur.size() + _ej, oc));
            }
        }
        vector<size_t> idx = sort_indexes(vals);
        for (long long _ek = 0; _ek < expandSpans.size() && _ek < vals.size(); _ek++) {
            long long period = id2period.at(idx.at(_ek));
            if (spans[_ek][0].second == INT32_MAX) {
                // copy from above
                long long slot = idx.at(_ek) / rest->occur.size();
                expandSpans[_ek].assign(begin(expandSpans[slot]), end(expandSpans[slot]));
            }
            expandSpans[_ek].push_back(make_pair(to_encode_edge(rest->node_a, rest->node_b), period));
            if (expandSpans[_ek][0].second > period) expandSpans[_ek][0].second = period;
            if (expandSpans[_ek][1].second < period) expandSpans[_ek][1].second = period;
        }
    }

    return expandSpans;
}

vector<vector<pair<long long, long long>>>
updatePeriod(const Graphs &g, const vector<vector<pair<long long, long long>>> &spans) {
    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;
    vector<vector<pair<long long, long long>>> expandSpans;
    expandSpans.assign(begin(spans), end(spans));

    assert(SIZE(spans) > 0);
    for (const auto &_p: spans[0]) {
        edges.insert(_p.first);
    }
    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge->node_a, edge->node_b)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }
    }

    for (const auto &edge: newRestEdges) {
        Edge *rest = edge.second;
        vector<long long> vals;
        unordered_map<long long, long long> id2period;
        for (long long _ei = 0; _ei < SIZE(spans); _ei++) {
            auto span = spans.at(_ei);
            for (long long _ej = 0; _ej < rest->occur.size(); _ej++) {
                long long oc = rest->occur.at(_ej);
                if (oc >= span[0].second || oc <= span[1].second) {
                    vals.push_back(abs(span[0].second - span[1].second));
                } else {
                    vals.push_back(abs(span[0].second - oc) > abs(span[1].second - oc) ?
                                   abs(span[0].second - oc) : abs(span[1].second - oc));
                }
                id2period.insert(make_pair(_ei * rest->occur.size() + _ej, oc));
            }
        }
        vector<size_t> idx = sort_indexes(vals);
        for (long long _ek = 0; _ek < expandSpans.size() && _ek < vals.size(); _ek++) {
            long long period = id2period.at(idx.at(_ek));
            if (spans[_ek][0].second == INT32_MAX) {
                // copy from above
                long long slot = idx.at(_ek) / rest->occur.size();
                expandSpans[_ek].assign(begin(expandSpans[slot]), end(expandSpans[slot]));
            }
            expandSpans[_ek].push_back(make_pair(to_encode_edge(rest->node_a, rest->node_b), period));
            if (expandSpans[_ek][0].second > period) expandSpans[_ek][0].second = period;
            if (expandSpans[_ek][1].second < period) expandSpans[_ek][1].second = period;
        }
    }

    return expandSpans;
}

void updateTruss(Graphs &g, Edge *edge, Truss &__truss) {
    g.newEdgeFrom(edge);
    long long maxK = max_element(begin(__truss), end(__truss),
                                 [](const pair<long long, long long> a, const pair<long long, long long> b) -> bool {
                                     return a.second > b.second;
                                 })->second;

    pair<long long, long long> k1k2pair = calculateK1K2(g, edge, __truss, maxK);

    assert(__truss.find(to_encode_edge(edge->node_a, edge->node_b)) == __truss.end());
    __truss[to_encode_edge(edge->node_a, edge->node_b)] = k1k2pair.first;
    maxK = k1k2pair.second;

    vector<vector<long long>> L(maxK - 2 + 1);
    long long u = edge->node_a, v = edge->node_b;
    for (const auto &node: neighbors(g, to_encode_edge(u, v))) {
        long long k = std::min(__truss.at(to_encode_edge(node, u)),
                               __truss.at(to_encode_edge(node, v)));
        if (k <= maxK) {
            if (__truss.at(to_encode_edge(node, u)) == k) {
                assert(k - 2 < L.size());
                L[k - 2].push_back(to_encode_edge(node, u));
            }
            if (__truss.at(to_encode_edge(node, v)) == k) {
                assert(k - 2 < L.size());
                L[k - 2].push_back(to_encode_edge(node, v));
            }
        }
    }

    for (long long _k = maxK; _k >= 2; --_k) {
        assert(_k - 2 < L.size());
        deque<long long> Q;
        for (const auto &_e: L[_k - 2]) Q.push_back(_e);
        unordered_map<long long, long long> s;
        while (!Q.empty()) {
            long long edgeCode = Q.front();
            auto _p = to_decode_edge(edgeCode);
            long long x = _p.first, y = _p.second;
            assert(x != y);
            Q.pop_front();
            s[edgeCode] = 0;
            for (const auto &z: neighbors(g, edgeCode)) {
                assert(__truss.find(to_encode_edge(z, x)) != __truss.end() &&
                       __truss.find(to_encode_edge(z, y)) != __truss.end());
                if (__truss.at(to_encode_edge(z, x)) < _k || __truss.at(to_encode_edge(z, y)) < _k) {
                    continue;
                }
                ++s[edgeCode];
                if (__truss.at(to_encode_edge(z, x)) == _k &&
                    std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(z, x)) == end(L[_k - 2])) {
                    Q.push_back(to_encode_edge(z, x));
                    L[_k - 2].push_back(to_encode_edge(z, x));
                }
                if (__truss.at(to_encode_edge(z, y)) == _k &&
                    std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(z, y)) == end(L[_k - 2])) {
                    Q.push_back(to_encode_edge(z, y));
                    L[_k - 2].push_back(to_encode_edge(z, y));
                }
            }
        } //end while Q
        auto it = std::find_if(begin(L[_k - 2]), end(L[_k - 2]),
                               [&](const long long &edgeHash) -> bool {
                                   assert(s.find(edgeHash) != s.end());
                                   return s.at(edgeHash) <= _k - 2;
                               });
        while (it != end(L[_k - 2])) {
            L[_k - 2].erase(it);
            auto _p = to_decode_edge(*it);
            for (const auto &z : neighbors(g, to_encode_edge(_p.first, _p.second))) {
                assert(__truss.find(to_encode_edge(_p.first, z)) != __truss.end() &&
                       __truss.find(to_encode_edge(_p.second, z)) != __truss.end());
                if (__truss.at(to_encode_edge(_p.first, z)) < _k ||
                    __truss.at(to_encode_edge(_p.second, z)) < _k) {
                    continue;
                }
                if (__truss.at(to_encode_edge(_p.first, z)) == _k &&
                    std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(_p.first, z)) == end(L[_k - 2])) {
                    continue;
                }
                if (__truss.at(to_encode_edge(_p.second, z)) == _k &&
                    std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(_p.second, z)) == end(L[_k - 2])) {
                    continue;
                }
                if (std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(_p.first, z)) != end(L[_k - 2])) {
                    --s[to_encode_edge(_p.first, z)];
                }
                if (std::find(begin(L[_k - 2]), end(L[_k - 2]), to_encode_edge(_p.second, z)) != end(L[_k - 2])) {
                    --s[to_encode_edge(_p.second, z)];
                }
            }
        }   // end while s[x, y] <= k - 2 in Lk
        for (const auto &edgeCode : L[_k - 2]) {
            assert(__truss.find(edgeCode) != __truss.end());
            __truss[edgeCode] = _k + 1;
        }
    }
}

pair<long long, long long> calculateK1K2(const Graphs &g, const Edge *edge, const Truss &truss, const long long maxK) {
    unordered_map<long long, long long> klevelTri;
    for (int _k = 2; _k <= maxK; _k++) {
        for (const auto &node : neighbors(g, to_encode_edge(edge->node_b, edge->node_a))) {
            assert(truss.find(to_encode_edge(node, edge->node_b)) != truss.end() &&
                   truss.find(to_encode_edge(node, edge->node_a)) != truss.end());
            if (truss.at(to_encode_edge(node, edge->node_a)) >= _k &&
                truss.at(to_encode_edge(node, edge->node_b)) >= _k) {
                ++klevelTri[_k];
            }
        }
    }
    long long k1 = 2, k2 = 2;
    for (int _k = 2; _k <= maxK; _k++) {
        if (klevelTri.find(_k) != klevelTri.end() && klevelTri.at(_k) >= _k - 2) {
            k1 = _k;
        }
        if (klevelTri.find(_k) != klevelTri.end() && klevelTri.at(_k) >= _k - 1) {
            k2 = _k + 1;
        }
    }
    if (debug_on) printf("k1 k2: %lld%lld%d \n", k1, k2); // debug
    return make_pair(k1, k2);
}

vector<long long> neighbors(const Graphs &g, long long edgeCode) {
    vector<long long> nei_nodes;
    auto pairs = to_decode_edge(edgeCode);

    unordered_set<long long> n_A;
    assert(g.id2node.find(pairs.first) != g.id2node.end() && g.id2node.find(pairs.second) != g.id2node.end());
    for (const auto &edge: g.id2node.at(pairs.first)->connTo) {
        long long _id = pairs.first == edge->node_b ? edge->node_a : edge->node_b;
        n_A.insert(_id);
    }

    for (const auto &edge: g.id2node.at(pairs.second)->connTo) {
        long long _id = pairs.second == edge->node_b ? edge->node_a : edge->node_b;
        if (n_A.find(_id) != n_A.end()) {
            if (_id == pairs.first || _id == pairs.second) continue;
            nei_nodes.push_back(_id);
        }
    }

    return nei_nodes;
}

bool graphEq(const Graphs &g1, const Graphs &g2) {
    return g1.nodes.size() == g2.nodes.size() && g1.edges.size() == g2.edges.size();
}

vector<vector<pair<long long, long long>>> MTCC(Graphs &g, long long _k, long long _topk, long long _query_node) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node, communities[0].nodes.size());
    }
    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<pair<long long, long long>>>, GraphsHash, GraphsComp> block2spans;
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = node_set.size() * (node_set.size() - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
        if (debug_on)
            printf("[%d]: find %lld-clique with query node %lld: %zu\n", __LINE__, k, query_node,
                   cand_k_clique_nodes.size());
        // find the smallest temporal clsuted community
        if (debug_on) printf(">>>>>>>>> find the smallest temporal clustered community >>>>>>\n");
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld ", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%d, ", oc);
                }
                printf("\n");
            }
            vector<vector<pair<long long, long long>>> spans = enmuMTCCPeriod(minimal_block, topk);
            std::sort(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                   const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            });
            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            assert(!spans.empty());
            long long least_interval = INT32_MAX;
            for (const auto &span : spans) {
                assert(span[1].second - span[0].second >= 0);
                if (span[0].second == INT32_MAX) continue; // MTCC not needed
                least_interval = std::min(least_interval, span[1].second - span[0].second);
                innerP2gs[span[1].second - span[0].second].emplace_back(minimal_block);
            }
            vector<vector<pair<long long, long long>>> leastSpans;
            for (const auto &span: spans) {
                if (span[1].second - span[0].second == least_interval) leastSpans.emplace_back(span);
            }
            block2spans.insert(make_pair(minimal_block, leastSpans));
            assert(innerP2gs.size() <= topk);


            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            _pit->second.emplace_back(_g);
                        }
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (debug_on) {
                if (!spans.empty()) {
                    printf("[%d]: minimal span size: %zu\n", __LINE__, SIZE(spans));
//                    for (int _i = 0; _i < SIZE(spans); _i++) {
//                        if (spans[_i][0].second == INT32_MAX) continue;
//                        printf("[%d]: minimal time period: %lld, min: %lld, max: %lld, ", __LINE__,
//                               spans[_i][1].second - spans[_i][0].second,
//                               spans[_i][0].second, spans[_i][1].second);
//                        for (int l = 2; l < spans[_i].size(); l++) {
//                            auto edge = to_decode_edge(spans[_i][l].first);
//                            printf("(%lld, %lld): %lld,", edge.first, edge.second, spans[_i][l].second);
//                        }
//                        printf("\n");
//                    }
                } // end if empty test
            }
        } // end for k-block loop
    }

    assert(p2gs.size() <= topk);
    // default set top-k = 1
    assert(!p2gs.empty());
    vector<Graphs> gs = p2gs.begin()->second;
//    vector<Graphs> ex_gs;
    vector<vector<pair<long long, long long>>> ans;
//    for (const auto &_g: gs) {
//        Graphs _gs;
//        vector<long long> _nodes;
//        std::transform(_g.nodes.begin(), _g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
//                       [](const Node* _n) -> long long {
//                           return _n->node_id;
//                       });
//        _gs.newGraphsFrom(_nodes, _g);
//        ex_gs.push_back(_gs);
//    }
    for (int _bi = 0; _bi < SIZE(gs); _bi++) {
        Graphs &B = gs.at(_bi);
        assert(block2community.find(B) != block2community.end());
        Graphs &community = block2community.at(B);
        assert(block2truss.find(B) != block2truss.end());
        Truss Btruss = block2truss.at(B);
        assert(block2spans.find(B) != block2spans.end());
        vector<vector<pair<long long, long long>>> spans = block2spans.at(B);

        if (debug_on) printf("%zu %zu\n", community.nodes.size(), community.edges.size());
//
//        vector<vector<pair<long long, long long>>> possible_ans = enmuMTCCPeriod(community, topk);
//
//        if (!possible_ans.empty() && abs(possible_ans[0][0].second - possible_ans[0][1].second) ==
//                                     abs(spans[0][0].second - spans[0][1].second)) {
//            for (const auto &_pa: possible_ans) ans.emplace_back(_pa);
//            continue;
//        }
        // graph expansion init
        B = B.deepCopy();
        unordered_set<long long> vistedNodes;
        deque<long long> Q;
        for (const auto &v: B.nodes) {
            vistedNodes.insert(v->node_id);
            Q.push_back(v->node_id);
        }
        // graph expansion
        while (vistedNodes.size() < community.nodes.size()) {
            long long _curNode = Q.front();
            Q.pop_front();

            for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                    vistedNodes.insert(outerNodes);
                    assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                           community.hashedEdge.end());
                    Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                    updateTruss(B, outerEdge, Btruss);
                    for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                        if (B.id2node.find(node) != B.id2node.end() &&
                            B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                            B.hashedEdge.end()) {
                            assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                   community.hashedEdge.end());
                            updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                        Btruss);
                        }
                    }
                    Q.push_back(outerNodes);
                    // detect k-truss maintain
                    bool bFound = true;
                    for (const auto &_perTruss: Btruss) {
                        if (debug_on) {
                            auto _p = to_decode_edge(_perTruss.first); // debug
                            printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                   _perTruss.second); //debug
                        }
                        if (_perTruss.second < k) {
                            bFound = false;
                            break;
                        }
                    }
                    if (bFound) {
                        vector<vector<pair<long long, long long>>> _s;
                        for (const auto &span: spans) {
                            auto exSpans = updateMTCCPeriod(B, span);
                            if (exSpans.empty()) {
                                ans.emplace_back(span);
                                goto L1;
                            } else {
                                for (const auto &ex: exSpans) {
                                    _s.emplace_back(ex);
                                }
                            }
                        }
                        spans.clear();
                        std::transform(_s.begin(), _s.end(), std::inserter(spans, spans.begin()),
                                       [](const vector<pair<long long, long long>> &v) -> vector<
                                               pair<long long, long long>> {
                                           return v;
                                       });
                    }   // end if bFound
                }
            }   // end for neighbor nodes
        } // end while expansion

        //community-level testing (which means the community is the final subgraph)
        for (const auto &span: spans) ans.emplace_back(span);

        L1:
        continue;
    } // end each community

    return ans;
}


vector<vector<pair<long long, long long>>>
updateMTCCPeriod(const Graphs &g, const vector<pair<long long, long long>> &span) {
    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;
    vector<vector<pair<long long, long long>>> expandSpans;

    assert(!span.empty());
    for (int _pi = 2; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge->node_a, edge->node_b)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }
    }

    vector<vector<pair<long long, long long>>> sat_edges(SIZE(newRestEdges));
    long long node_seq = 0;
    for (const auto &edge: newRestEdges) {
        Edge *rest = edge.second;
        for (long long _ej = 0; _ej < SIZE(rest->occur); _ej++) {
            long long oc = rest->occur.at(_ej);
            if (oc >= span[0].second && oc <= span[1].second) {
                sat_edges[node_seq].push_back(
                        make_pair(to_encode_edge(rest->node_b, rest->node_a), rest->occur.at(_ej)));
            }
        }
        ++node_seq;
    }

    long long pos_val = 1;
    for (const auto &sat: sat_edges) {
        pos_val *= SIZE(sat);
    }

    if (pos_val == 0) {
        return expandSpans;
    }
    vector<vector<pair<long long, long long>>> _s;
    vector<pair<long long, long long>> pos;
    enumUpdation(0, sat_edges, pos, _s);

    for (const auto &_: _s) {
        vector<pair<long long, long long>> init(begin(span), end(span));
        for (const auto &_ele: _) init.emplace_back(_ele);
        expandSpans.emplace_back(init);
    }
    return expandSpans;
}

vector<vector<pair<long long, long long>>>
expandMTCCPeriodNotEmpty(const Graphs &g, const vector<pair<long long, long long>> &span, const long long &topk) {
    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;
    vector<vector<pair<long long, long long>>> expandSpans;
    vector<vector<pair<long long, long long>>> container;

    assert(!span.empty());
    for (int _pi = 2; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge->node_a, edge->node_b)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }
    }

    assert(SIZE(newRestEdges) > 1);
    Edge *edge = newRestEdges.begin()->second;
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) init_intervals.emplace_back(oc);

    for (int _i = 1; _i < SIZE(newRestEdges); ++_i) {
        auto iter = newRestEdges.begin();
        std::advance(iter, _i);
        Edge *cur_edge = iter->second;
        vector<long long> vals;
        if (_i == 1) {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ei = 0; _ei < SIZE(init_intervals); ++_ei) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); ++_ej) {
                    vals.emplace_back(abs(init_intervals.at(_ei) - cur_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ej + _ei * SIZE(cur_edge->occur),
                                              make_pair(init_intervals.at(_ei), cur_edge->occur.at(_ej))));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            long long minInterval = vals.at(idx.at(0));
            long long _curTopk = 0;
            for (int _idx = 0; _idx < SIZE(idx); ++_idx) {
                if (vals.at(idx.at(_idx)) > minInterval) {
                    minInterval = vals.at(idx.at(_idx));
                    ++_curTopk;
                }
                if (_curTopk >= topk) break;
                vector<pair<long long, long long>> span(2, pair<long long, long long>(0, INT32_MAX));
                pair<long long, long long> intervals = id2edges.at(idx.at(_idx));
                // 0: Min, 1: Max
                span[0].second = std::min(intervals.first, intervals.second);
                span[1].second = std::max(intervals.first, intervals.second);
                span.emplace_back(to_encode_edge(edge->node_a, edge->node_b), intervals.first);
                span.emplace_back(to_encode_edge(cur_edge->node_a, cur_edge->node_b), intervals.second);
                assert(span[1].second - span[0].second == minInterval);
                container.push_back(span);
            }
        } else {
            unordered_map<long long, long long> id2period;
            for (long long _ek = 0; _ek < SIZE(container); _ek++) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); _ej++) {
                    if (container[_ek][0].second <= cur_edge->occur.at(_ej) &&
                        container[_ek][1].second >= cur_edge->occur.at(_ej)) {
                        vals.push_back(abs(container[_ek][0].second - container[_ek][1].second));
                    } else {
                        vals.push_back(abs(container[_ek][0].second - cur_edge->occur.at(_ej)) >
                                       abs(container[_ek][1].second - cur_edge->occur.at(_ej)) ?
                                       abs(container[_ek][0].second - cur_edge->occur.at(_ej)) : abs(
                                        container[_ek][1].second - cur_edge->occur.at(_ej)));
                    }
                    id2period.insert(make_pair(_ek * cur_edge->occur.size() + _ej, cur_edge->occur.at(_ej)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            vector<vector<pair<long long, long long>>> _c;
            long long minInterval = vals.at(idx.at(0));
            long long _curTopk = 0;
            for (unsigned long _idx : idx) {
                if (vals.at(_idx) > minInterval) {
                    minInterval = vals.at(_idx);
                    ++_curTopk;
                }
                if (_curTopk >= topk) break;
                assert(id2period.find(_idx) != id2period.end());
                long long interval = id2period.at(_idx);
                long long slot = _idx / SIZE(cur_edge->occur);
                vector<pair<long long, long long>> _span;
                _span.assign(begin(container[slot]), end(container[slot]));
                _span.emplace_back(make_pair(to_encode_edge(cur_edge->node_b, cur_edge->node_a), interval));
                if (_span[0].second > interval) _span[0].second = interval;
                if (_span[1].second < interval) _span[1].second = interval;

                _c.emplace_back(_span);
            }

            // update top-k storage
            container.clear();
            for (const auto &_: _c) {
                container.emplace_back(_);
            }
        } // end else
    }

    for (const auto &_: container) {
        vector<pair<long long, long long>> init(begin(span), end(span));
        for (const auto &_ele: _) init.emplace_back(_ele);

        init[1].second = std::max_element(begin(init) + 2, end(init), [](const pair<long long, long long> &a,
                                                                         const pair<long long, long long> &b) -> bool {
            return a.second < b.second;
        })->second;
        init[0].second = std::min_element(begin(init) + 2, end(init), [](const pair<long long, long long> &a,
                                                                         const pair<long long, long long> &b) -> bool {
            return a.second < b.second;
        })->second;

        expandSpans.emplace_back(init);
    }
    return expandSpans;
}

vector<vector<pair<long long, long long>>>
updateMTCCPeriodNotEmpty(const Graphs &g, const vector<pair<long long, long long>> &span, const long long &topk) {
    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;
    vector<vector<pair<long long, long long>>> expandSpans;

    assert(!span.empty());
    for (int _pi = 2; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge->node_a, edge->node_b)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }
    }

    /*
     * expansion contribution calculation
     */
    assert(span[1].second - span[0].second >= 0);
    unordered_map<long long, vector<long long>> upperMaxBound;
    unordered_map<long long, vector<long long>> lowerMinBound;
    long long cur_expansion_length = span[1].second - span[0].second;
    long long cur_max_lit = span[1].second;
    long long cur_min_lit = span[0].second;
    set<long long> relative_expansion;

    long long step = 0;

    for (const auto &edge: newRestEdges) {
        auto *rest = edge.second;
        for (const auto &oc: rest->occur) {
            upperMaxBound[to_encode_edge(rest->node_a, rest->node_b)].emplace_back(oc - cur_max_lit);
            lowerMinBound[to_encode_edge(rest->node_a, rest->node_b)].emplace_back(cur_min_lit - oc);
        }
    }

    for (const auto &exp: upperMaxBound) {
        long long max_val_in_edge = *(std::max_element(begin(exp.second), end(exp.second)));
        if (max_val_in_edge > 0) {
            for (const auto &val: exp.second) {
                if (val >= cur_min_lit && val <= cur_max_lit) {
                    step++;
                    break;
                }
            }
            relative_expansion.insert(max_val_in_edge);
        }
    }
    for (const auto &exp: lowerMinBound) {
        long long max_val_in_edge = *(std::max_element(begin(exp.second), end(exp.second)));
        if (max_val_in_edge > 0) {
            for (const auto &val: exp.second) {
                if (val >= cur_min_lit && val <= cur_max_lit) {
                    step++;
                    break;
                }
            }
            relative_expansion.insert(max_val_in_edge);
        }
    }

    for (const auto &max_exp: upperMaxBound) {
        for (const auto &min_exp: lowerMinBound) {
            if (max_exp.first == min_exp.first) continue;
            long long max_val_upper_in_edge = *(std::max_element(begin(max_exp.second), end(max_exp.second)));
            long long max_val_lower_in_edge = *(std::max_element(begin(min_exp.second), end(min_exp.second)));

            if (max_val_lower_in_edge <= 0 || max_val_upper_in_edge <= 0) continue;

            relative_expansion.insert(max_val_lower_in_edge + max_val_upper_in_edge);
        }
    }

    auto iter = relative_expansion.begin();
    if (SIZE(relative_expansion) > topk) {
        std::advance(iter, topk - 1);
    } else {
        std::advance(iter, SIZE(relative_expansion) - 1);
    }
    long long topk_relative_expansion = *iter;

    vector<vector<pair<long long, long long>>> exp_edges(SIZE(newRestEdges));
    long long node_seq = 0;
    long long overflow_warning = 1;
    for (const auto &edge: newRestEdges) {
        Edge *rest = edge.second;
        overflow_warning *= SIZE(rest->occur);
        for (long long _ej = 0; _ej < SIZE(rest->occur); _ej++) {
            if ((rest->occur.at(_ej) <= span[1].second && rest->occur.at(_ej) >= span[0].second) ||
                (std::max(std::abs(span[1].second - rest->occur.at(_ej)),
                          std::abs(span[0].second - rest->occur.at(_ej))) <=
                 cur_expansion_length + topk_relative_expansion)) {
                exp_edges[node_seq].push_back(
                        make_pair(to_encode_edge(rest->node_b, rest->node_a), rest->occur.at(_ej)));
            }
        }
        ++node_seq;
    }
    vector<vector<pair<long long, long long>>> _s;
    vector<pair<long long, long long>> pos;
    assert(overflow_warning < INT64_MAX);
    enumUpdation(0, exp_edges, pos, _s);

    for (const auto &_: _s) {
        vector<pair<long long, long long>> init(begin(span), end(span));
        for (const auto &_ele: _) init.emplace_back(_ele);

        init[1].second = std::max_element(begin(init) + 2, end(init), [](const pair<long long, long long> &a,
                                                                         const pair<long long, long long> &b) -> bool {
            return a.second < b.second;
        })->second;
        init[0].second = std::min_element(begin(init) + 2, end(init), [](const pair<long long, long long> &a,
                                                                         const pair<long long, long long> &b) -> bool {
            return a.second < b.second;
        })->second;

        expandSpans.emplace_back(init);
    }
    return expandSpans;
}

void enumUpdation(const long long c, const vector<vector<pair<long long, long long>>> &vals,
                  vector<pair<long long, long long>> &pos, vector<vector<pair<long long, long long>>> &_s) {
    if (c == SIZE(vals)) {
        _s.emplace_back(pos);
        return;
    }

    for (const auto &val: vals[c]) {
        pos.emplace_back(val);
        enumUpdation(c + 1, vals, pos, _s);
        pos.erase(pos.begin() + pos.size() - 1);
    }
}


long long find_idx_by_range(const long long &idx, const vector<long long> &vec) {
    vector<long long> partial;
    std::partial_sum(vec.begin(), vec.end(), partial.begin(), [](const long long &a, const long long &b) -> long long {
        return a + b - 1;
    });
    long long val = SIZE(partial) - 1;
    for (long long _idx = 0; _idx < SIZE(partial); ++_idx) {
        if (partial.at(_idx) > idx) {
            val = idx - 1;
            break;
        }
    }
    return val;
}

void log_results(vector<vector<pair<long long, long long>>> &res, FILE *fp) {
    std::sort(begin(res), end(res),
              [](const vector<pair<long long, long long>> &a, const vector<pair<long long, long long>> &b) -> bool {
                  return a.at(1).second - a.at(0).second < b.at(1).second - b.at(0).second;
              });

    string offical_lang = "========================generating report==============================\n";
    fp != nullptr ? fprintf(fp, "%s", offical_lang.c_str()) : printf("%s", offical_lang.c_str());
    fp != nullptr ? fprintf(fp, "finding MTCC with %zu\n", res.size()) : printf("finding MTCC with %zu\n", res.size());
    for (const auto &_res: res) {
        printf("length: %lld, ", _res.at(1).second - _res.at(0).second);
        for (int _ri = 2; _ri < SIZE(_res); _ri++) {
            auto path = _res.at(_ri);
            auto _p = to_decode_edge(path.first);
            fp != nullptr ? fprintf(fp, "(%lld, %lld): %lld, ", _p.first, _p.second, path.second) : printf(
                    "(%lld, %lld): %lld, ", _p.first, _p.second, path.second);
        }
        fp != nullptr ? fprintf(fp, "\n") : printf("\n");
    }
}

void log_results(vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>> &res, FILE *fp) {
    string offical_lang = "========================generating report==============================\n";
    fp != nullptr ? fprintf(fp, "%s", offical_lang.c_str()) : printf("%s", offical_lang.c_str());
    fp != nullptr ? fprintf(fp, "finding TCC with %zu Communities.\n", res.size()) : printf("finding MTCC with %d\n",
                                                                                            SIZE(res));
    for (long long _i = 0; _i < SIZE(res); _i++) {
        auto span = res.at(_i).first;
        auto info = res.at(_i).second;
        fp != nullptr ? fprintf(fp, "length: %lld, ", info.second - info.first) : printf("length: %lld, ",
                                                                                         info.second - info.first);
        for (int _ri = 0; _ri < SIZE(span); _ri++) {
            auto path = span.at(_ri);
            auto _p = to_decode_edge(path.first);
            fp != nullptr ? fprintf(fp, "(%lld, %lld): (, ", _p.first, _p.second) : printf(
                    "(%lld, %lld): (, ", _p.first, _p.second);
            for (const auto &oc: path.second) {
                fp != nullptr ? fprintf(fp, "%lld, ", oc) : printf("%lld, ", oc);
            }
            fp != nullptr ? fprintf(fp, "), ") : printf("), ");
        }
        fp != nullptr ? fprintf(fp, "\n") : printf("\n");
    }
}

pair<long long, vector<long long>> reCalculateRank(const Graphs &g, const long long topk) {
    deque<pair<long long, long long>> Q;
    assert(SIZE(g.edges) > 0);
    auto it = g.edges.begin();
    for (const auto &e:  (*it)->occur) Q.emplace_back(e, e);
    for (int i = 1; i < SIZE(g.edges); ++i) {
        deque<pair<long long, long long>> _Qtp;
        auto curEdge = g.edges.at(i);
        while (!Q.empty()) {
            for (const auto &curOc: curEdge->occur) {
                auto minmax = Q.front();
                if (minmax.first > curOc) minmax.first = curOc;
                if (minmax.second < curOc) minmax.second = curOc;

                _Qtp.push_back(minmax);
            }

            Q.pop_front();
        }
        std::sort(begin(_Qtp), end(_Qtp),
                  [](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                      return a.second - a.first < b.second - b.first;
                  });
        _Qtp.resize(std::distance(_Qtp.begin(), std::unique(_Qtp.begin(), _Qtp.end())));
        if (SIZE(_Qtp) < topk) {
            Q.assign(begin(_Qtp), end(_Qtp));
        } else {
            Q.assign(begin(_Qtp), begin(_Qtp) + topk);
        }
    }
    assert(SIZE(Q) > 0);
    auto rank = [&](const deque<pair<long long, long long>> &Q) -> vector<long long> {
        vector<long long> _r;
        for (const auto &e: Q) {
            assert(e.second >= e.first);
            _r.push_back(e.second - e.first);
        }
        return _r;
    }(Q);

    return make_pair(SIZE(Q), rank);
}

pair<long long, long long> calculateRank(const Graphs &g) {
    long long possibilities = 1;
    long long MAX = INT32_MIN, MIN = INT32_MAX;
    for (const auto &e: g.edges) {
        possibilities *= SIZE(e->occur);
        long long cur_max = *std::max_element(begin(e->occur), end(e->occur));
        long long cur_min = *std::min_element(begin(e->occur), end(e->occur));
        MAX = cur_max > MAX ? cur_max : MAX;
        MIN = cur_min < MIN ? cur_min : MIN;
    }

    assert(possibilities > 0);
    assert(MAX - MIN >= 0);
    return make_pair(possibilities, MAX - MIN);
}


bool inInterval(const vector<pair<long long, long long>> &c, const long long val) {
    bool bFind = false;
    for (const auto &p : c) {
        if (val >= p.first && val <= p.second) {
            bFind = true;
            break;
        }
    }

    return bFind;
}

void updateGraphByUpperBound(Graphs &g, const long long upper, const long long query_node, FILE *fp) {
    unordered_set<long long> delEdges;
    vector<pair<long long, long long>> c;
    assert(g.id2node.find(query_node) != g.id2node.end());
    long long aux_rec = 0;
    for (const auto &edge: g.id2node.at(query_node)->connTo)
        for (const auto &oc: edge->occur)
            c.emplace_back(make_pair(oc - upper, oc + upper));
    for (auto &edge: g.edges) {
        auto iter = edge->occur.begin();
        for (; iter != edge->occur.end();) {
            if (!inInterval(c, *iter)) {
                iter = edge->occur.erase(iter);
                aux_rec++;
            } else {
                iter++;
            }
        }

        if (edge->occur.empty()) {
            delEdges.insert(to_encode_edge(edge->node_a, edge->node_b));
        }
    }
    if (debug_info) {
        printf("[%d]: prunning %lld edges\n", __LINE__, aux_rec);
        if (fp != nullptr) {
            fprintf(fp, "Prunning %lld edges\n", aux_rec);
        }
    }
    for (const auto &edgeCode: delEdges) {
        assert(g.hashedEdge.find(edgeCode) != g.hashedEdge.end());
        Edge *edge = g.hashedEdge.at(edgeCode);
        long long nodeA = edge->node_a, nodeB = edge->node_b;
        g.id2node.at(nodeA)->connTo.erase(
                std::find(g.id2node.at(nodeA)->connTo.begin(), g.id2node.at(nodeA)->connTo.end(), edge));
        g.id2node.at(nodeB)->connTo.erase(
                std::find(g.id2node.at(nodeB)->connTo.begin(), g.id2node.at(nodeB)->connTo.end(), edge));
        g.edges.erase(std::remove(g.edges.begin(), g.edges.end(), edge), g.edges.end());
        g.hashedEdge.erase(edgeCode);
    }
}

vector<vector<pair<long long, long long>>>
MTCC_Fast(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<pair<long long, long long>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = node_set.size() * (node_set.size() - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            community2graphs[community].push_back(minimal_block);
        } // end for k-block loop
    }

    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (!reduction_fast) {
        vector<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = calculateRank(minimal_block);
                if (topk <= info.first) {
                    maxVal.push_back(info.second);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk);
                    maxVal.push_back(calculateRank(minimal_block).second);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        //    timers->end("Max-Min");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        //    timers->start();
        vector<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.push_back(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.push_back(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
//        timers->end("Topk-Retrival");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    }
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    community2graphs.clear();

    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node);
    CUtility *timer = new CUtility();
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%lld]: max truss is: %lld\n", max_truss, __LINE__);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }

    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = node_set.size() * (node_set.size() - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
        if (debug_on)
            printf("[%d]: find %lld-clique with query node %lld: %zu\n", __LINE__, k, query_node,
                   cand_k_clique_nodes.size());
        // find the smallest temporal clsuted community
        if (debug_on) printf("[%d]:>>>>>>>>> find the smallest temporal clusted community >>>>>>\n", __LINE__);
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%d, ", oc);
                }
                printf("\n");
            }
            vector<vector<pair<long long, long long>>> spans = enmuMTCCPeriod(minimal_block, topk);
            std::sort(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                   const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            });
            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            assert(!spans.empty());
            long long least_interval = INT32_MAX;
            for (const auto &span : spans) {
                assert(span[1].second - span[0].second >= 0);
                if (span[0].second == INT32_MAX) continue; // MTCC not needed
                least_interval = std::min(least_interval, span[1].second - span[0].second);
                innerP2gs[span[1].second - span[0].second].emplace_back(minimal_block);
            }
            vector<vector<pair<long long, long long>>> leastSpans;
            for (const auto &span: spans) {
                if (span[1].second - span[0].second == least_interval) leastSpans.emplace_back(span);
            }
            block2spans.insert(make_pair(minimal_block, leastSpans));
            assert(innerP2gs.size() <= topk);
            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            _pit->second.emplace_back(_g);
                        }
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (debug_on) {
                if (!spans.empty()) {
                    printf("[%d]: minimal span size: %zu\n", __LINE__, SIZE(spans));
                    for (int _i = 0; _i < SIZE(spans); _i++) {
                        if (spans[_i][0].second == INT32_MAX) continue;
                        printf("[%d]: minimal time period: %lld, min: %lld, max: %lld, ", __LINE__,
                               spans[_i][1].second - spans[_i][0].second,
                               spans[_i][0].second, spans[_i][1].second);
                        for (int l = 2; l < spans[_i].size(); l++) {
                            auto edge = to_decode_edge(spans[_i][l].first);
                            printf("(%lld, %lld): %lld,", edge.first, edge.second, spans[_i][l].second);
                        }
                        printf("\n");
                    }
                } // end if empty test
            }
        } // end for k-block loop
    }


    assert(p2gs.size() <= topk);
    // default set top-k = 1
    assert(!p2gs.empty());
    vector<Graphs> gs = p2gs.begin()->second;
//    vector<Graphs> ex_gs;
    vector<vector<pair<long long, long long>>> ans;
//    for (const auto &_g: gs) {
//        Graphs _gs;
//        vector<long long> _nodes;
//        std::transform(_g.nodes.begin(), _g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
//                       [](const Node* _n) -> long long {
//                           return _n->node_id;
//                       });
//        _gs.newGraphsFrom(_nodes, _g);
//        ex_gs.push_back(_gs);
//    }
    for (int _bi = 0; _bi < SIZE(gs); _bi++) {
        Graphs &B = gs.at(_bi);
        assert(block2community.find(B) != block2community.end());
        Graphs &community = block2community.at(B);
        assert(block2truss.find(B) != block2truss.end());
        Truss Btruss = block2truss.at(B);
        assert(block2spans.find(B) != block2spans.end());
        vector<vector<pair<long long, long long>>> spans = block2spans.at(B);
        if (debug_on) printf("%zu %zu\n", community.nodes.size(), community.edges.size());


//        vector<vector<pair<long long, long long>>> possible_ans = enmuMTCCPeriod(community, topk);
//        if (!possible_ans.empty() && abs(possible_ans[0][0].second - possible_ans[0][1].second) ==
//                                     abs(spans[0][0].second - spans[0][1].second)) {
//            for (const auto &_pa: possible_ans) ans.emplace_back(_pa);
//            continue;
//        }

        // graph expansion init
        B.deepCopy();
        unordered_set<long long> vistedNodes;
        deque<long long> Q;
        for (const auto &v: B.nodes) {
            vistedNodes.insert(v->node_id);
            Q.push_back(v->node_id);
        }

        // graph expansion
        while (vistedNodes.size() < community.nodes.size()) {
            long long _curNode = Q.front();
            Q.pop_front();

            for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                    vistedNodes.insert(outerNodes);
                    assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                           community.hashedEdge.end());
                    Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                    updateTruss(B, outerEdge, Btruss);
                    for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                        if (B.id2node.find(node) != B.id2node.end() &&
                            B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                            B.hashedEdge.end()) {
                            assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                   community.hashedEdge.end());
                            updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                        Btruss);
                        }
                    }
                    Q.push_back(outerNodes);
                    // detect k-truss maintain
                    bool bFound = true;
                    for (const auto &_perTruss: Btruss) {
                        if (debug_on) {
                            auto _p = to_decode_edge(_perTruss.first); // debug
                            printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                   _perTruss.second); //debug
                        }
                        if (_perTruss.second < k) {
                            bFound = false;
                            break;
                        }
                    }
                    if (bFound) {
                        vector<vector<pair<long long, long long>>> _s;
                        for (const auto &span: spans) {
                            auto exSpans = updateMTCCPeriod(B, span);
                            if (exSpans.empty()) {
                                ans.emplace_back(span);
                                goto L1;
                            } else {
                                for (const auto &ex: exSpans) {
                                    _s.emplace_back(ex);
                                }
                            }
                        }
                        spans.clear();
                        std::transform(_s.begin(), _s.end(), std::inserter(spans, spans.begin()),
                                       [](const vector<pair<long long, long long>> &v) -> vector<
                                               pair<long long, long long>> {
                                           return v;
                                       });
                    }   // end if bFound
                }
            }   // end for neighbor nodes
        } // end while expansion
        //community-level testing (which means the community is the final subgraph)
        for (const auto &span: spans) ans.emplace_back(span);

        L1:
        continue;
    } // end each community

    timer->end(reduction_fast ? "MTCC-Fast2 INNER" : "MTCC-Fast2 INNER");
    return ans;
}

void graphExpansion(Graphs &B, Truss &Btruss, const Graphs &community, const long long k, const long long topk,
                    bool reduction) {
    // graph expansion init
    unordered_set<long long> vistedNodes;
    deque<long long> Q;
    for (const auto &v: B.nodes) {
        vistedNodes.insert(v->node_id);
        Q.push_back(v->node_id);
    }

    // graph expansion
    while (vistedNodes.size() < community.nodes.size()) {
        long long _curNode = Q.front();
        Q.pop_front();

        for (const auto &outer: community.id2node.at(_curNode)->connTo) {
            long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
            if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                vistedNodes.insert(outerNodes);
                assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                       community.hashedEdge.end());
                Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                updateTruss(B, outerEdge, Btruss);
                for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                    if (B.id2node.find(node) != B.id2node.end() &&
                        B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                        B.hashedEdge.end()) {
                        assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                               community.hashedEdge.end());
                        updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                    Btruss);
                    }
                }
                Q.push_back(outerNodes);
                // detect k-truss maintain
                bool bFound = true;
                for (const auto &_perTruss: Btruss) {
                    if (debug_on) {
                        auto _p = to_decode_edge(_perTruss.first); // debug
                        printf("[%d]:(%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                               _perTruss.second); //debug
                    }
                    if (_perTruss.second < k) {
                        bFound = false;
                        break;
                    }
                }
                if (bFound) {
                    if (!reduction) {
                        if (topk <= calculateRank(B).first) {
                            goto EndFlag;
                        }
                    } else {
                        if (topk <= reCalculateRank(B, topk).first) {
                            goto EndFlag;
                        }
                    };
                }   // end if bFound
            }
        }   // end for neighbor nodes
    } // end while expansion

    EndFlag:;
}

vector<vector<pair<long long, long long>>> TopKTCC(Graphs &g, long long _k, long long _topk, long long _query_node) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %d\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node, communities[0].nodes.size());
    }
    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, unordered_map<long long, vector<vector<pair<long long, long long>>>>, GraphsHash, GraphsComp> block2spans;
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = SIZE(node_set) * (SIZE(node_set) - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
        if (debug_on)
            printf("[%d]: find %lld-clique with query node %lld: %zu\n", __LINE__, k, query_node,
                   cand_k_clique_nodes.size());
        // find the smallest temporal clsuted community
        if (debug_on) printf(">>>>>>>>> find the smallest temporal clustered community >>>>>>\n");
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld ", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%d, ", oc);
                }
                printf("\n");
            }
            vector<vector<pair<long long, long long>>> spans = enmuMTCCPeriod(minimal_block, topk);
            std::sort(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                   const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            });
            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            assert(!spans.empty());
            // assert that the array is strictly sorted
            assert(is_sorted(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                          const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            }));
            long long curRank = 0;
            long long curMin = spans[0][1].second - spans[0][0].second;
            innerP2gs[curMin].emplace_back(minimal_block);
            unordered_map<long long, vector<vector<pair<long long, long long>>>> topKSpans;
            for (const auto &span : spans) {
                assert(span[1].second - span[0].second >= 0);
                if (span[0].second == INT32_MAX) continue; // MTCC not needed
                if (span[1].second - span[0].second > curMin) {
                    ++curRank;
                    curMin = span[1].second - span[0].second;
                    innerP2gs[curMin].emplace_back(minimal_block);
                }
                if (curRank >= topk) break;
                topKSpans[curRank].emplace_back(span);
            }
            assert(SIZE(topKSpans) <= topk);
            block2spans.insert(make_pair(minimal_block, topKSpans));
            assert(innerP2gs.size() <= topk);

            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            _pit->second.emplace_back(_g);
                        }
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (debug_on) {
                if (!spans.empty()) {
                    printf("[%d]: minimal span size: %d\n", __LINE__, SIZE(spans));
//                    for (int _i = 0; _i < SIZE(spans); _i++) {
//                        if (spans[_i][0].second == INT32_MAX) continue;
//                        printf("[%d]: minimal time period: %lld, min: %lld, max: %lld, ", __LINE__,
//                               spans[_i][1].second - spans[_i][0].second,
//                               spans[_i][0].second, spans[_i][1].second);
//                        for (int l = 2; l < spans[_i].size(); l++) {
//                            auto edge = to_decode_edge(spans[_i][l].first);
//                            printf("(%lld, %lld): %lld,", edge.first, edge.second, spans[_i][l].second);
//                        }
//                        printf("\n");
//                    }
                } // end if empty test
            }
        } // end for k-block loop
    }

    assert(p2gs.size() <= topk);
    assert(!p2gs.empty());
//    vector<Graphs> ex_gs;
    vector<vector<pair<long long, long long>>> ans;
//    for (const auto &_g: gs) {
//        Graphs _gs;
//        vector<long long> _nodes;
//        std::transform(_g.nodes.begin(), _g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
//                       [](const Node* _n) -> long long {
//                           return _n->node_id;
//                       });
//        _gs.newGraphsFrom(_nodes, _g);
//        ex_gs.push_back(_gs);
//    }
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    for (const auto &gs: p2gs) {
        for (const auto &g : gs.second) {
            g2rank[g] = 0;
        }
    }
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(g2rank.find(B) != g2rank.end());
            vector<vector<pair<long long, long long>>> spans = block2spans.at(B)[g2rank[B]++];

            if (findTopkVal(ans, topk) < findTopkVal(spans, 1)) {
                continue;
            }
            if (debug_on) printf("%zu %zu\n", community.nodes.size(), community.edges.size());

            // graph expansion init
            B = B.deepCopy();
            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (vistedNodes.size() < community.nodes.size()) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            vector<vector<pair<long long, long long>>> _s;
                            for (const auto &span: spans) {
                                auto exSpans = updateMTCCPeriod(B, span);
                                if (exSpans.empty()) {
                                    set<long long> enlargeRank;
                                    ans.emplace_back(span);
                                    auto enlargeSpans = updateMTCCPeriodNotEmpty(B, span, topk);
                                    unordered_map<long long, vector<vector<pair<long long, long long>>>> _tmp;
                                    for (const auto &elSpan: enlargeSpans) {
                                        enlargeRank.insert(elSpan[1].second - elSpan[0].second);
                                        _tmp[elSpan[1].second - elSpan[0].second].push_back(elSpan);
                                    }
                                    long long _i = 0;
                                    for (const auto &interval: enlargeRank) {
                                        if (_i >= topk) break;
                                        assert(_tmp.find(interval) != _tmp.end());
                                        for (const auto &_span: _tmp.at(interval))
                                            _s.emplace_back(_span);
                                        _i++;
                                    }
                                } else {
                                    for (const auto &ex: exSpans) {
                                        _s.emplace_back(ex);
                                    }
                                }
                            }
                            spans.clear();
                            std::transform(_s.begin(), _s.end(), std::inserter(spans, spans.begin()),
                                           [](const vector<pair<long long, long long>> &v) -> vector<
                                                   pair<long long, long long>> {
                                               return v;
                                           });
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } // end while expansion
            //community-level testing (which means the community is the final subgraph)
            for (const auto &span: spans) ans.emplace_back(span);
        } // end each community
    }   // topk question
    std::sort(begin(ans), end(ans),
              [](const vector<pair<long long, long long>> &a, const vector<pair<long long, long long>> &b) -> bool {
                  return a.at(1).second - a.at(0).second < b.at(1).second - b.at(0).second;
              });
    long long _recVal = findTopkVal(ans, topk);
    auto iter = ans.rbegin();
    for (; iter != ans.rend(); iter++) {
        if ((*iter)[1].second - (*iter)[0].second == _recVal) break;
    }
    ans.resize(std::distance(iter, ans.rend()));
    return ans;
}

vector<vector<pair<long long, long long>>>
TopKTCC_Fast(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }

    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, unordered_map<long long, vector<vector<pair<long long, long long>>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = SIZE(node_set) * (node_set.size() - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            community2graphs[community].push_back(minimal_block);
        } // end for k-block loop
    }
//
    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (!reduction_fast) {
        vector<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = calculateRank(minimal_block);
                if (topk <= info.first) {
                    maxVal.push_back(info.second);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk);
                    maxVal.push_back(calculateRank(minimal_block).second);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        //    timers->end("Max-Min");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        //    timers->start();
        set<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.insert(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.insert(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
//        timers->end("Topk-Retrival");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    }

    if (debug_info) printf("[%d]:finishing UpperBound calculation\n", __LINE__);
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    community2graphs.clear();

    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node);
    auto *timer = new CUtility();
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    if (debug_info) {
        printf("[%d]: finishing community search\n", __LINE__);
    }
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        vector<vector<long long>> cand_k_clique_nodes;
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        for (auto &knodes : k_clique_nodes) {
            unordered_set<long long> node_set;
            knodes.push_back(query_node); // 增加查询节点
            for (const auto &node: knodes) {
                node_set.insert(node);
            }

            long long ver_edges = SIZE(node_set) * (node_set.size() - 1) / 2;
            long long rel_edge = 0;
            for (const auto &n: knodes) {
                assert(community.id2node.find(n) != community.id2node.end());
                for (const auto &edge: community.id2node.at(n)->connTo) {
                    long long nei_node = edge->node_a == n ? edge->node_b : edge->node_a;
                    if (node_set.find(nei_node) != node_set.end()) {
                        ++rel_edge;
                    }
                }
            }
            rel_edge /= 2;
            if (debug_on) printf("[%d]: ver_edges: %lld, rel_edge: %lld\n", __LINE__, ver_edges, rel_edge);

            if (rel_edge == ver_edges) { // indicating a minimal truss
                cand_k_clique_nodes.push_back(knodes);
            }
        }
        if (debug_on)
            printf("[%d]: find %lld-clique with query node %lld: %zu\n", __LINE__, k, query_node,
                   cand_k_clique_nodes.size());
        // find the smallest temporal clsuted community
        if (debug_on) printf("[%d]:>>>>>>>>> find the smallest temporal clusted community >>>>>>\n", __LINE__);
        for (const auto &knode: cand_k_clique_nodes) {
            Graphs minimal_block;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            Truss minimalTruss;
            minimal_block.newGraphsFrom(knode, community);
            truss_decomposition(minimal_block, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: minimal_block.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: minimal_block.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%d, ", oc);
                }
                printf("\n");
            }
            vector<vector<pair<long long, long long>>> spans = enmuMTCCPeriod(minimal_block, topk);
            std::sort(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                   const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            });
            block2community.insert(make_pair(minimal_block, community));
            block2truss.insert(make_pair(minimal_block, minimalTruss));
            assert(!spans.empty());
            // assert that the array is strictly sorted
            assert(is_sorted(begin(spans), end(spans), [](const vector<pair<long long, long long>> &v1,
                                                          const vector<pair<long long, long long>> &v2) -> bool {
                return v1[1].second - v1[0].second < v2[1].second - v2[0].second;
            }));
            long long curRank = 0;
            long long curMin = spans[0][1].second - spans[0][0].second;
            innerP2gs[curMin].emplace_back(minimal_block);
            unordered_map<long long, vector<vector<pair<long long, long long>>>> topKSpans;
            for (const auto &span : spans) {
                assert(span[1].second - span[0].second >= 0);
                if (span[0].second == INT32_MAX) continue; // MTCC not needed
                if (span[1].second - span[0].second > curMin) {
                    ++curRank;
                    curMin = span[1].second - span[0].second;
                    innerP2gs[curMin].emplace_back(minimal_block);
                }
                if (curRank >= topk) break;
                topKSpans[curRank].emplace_back(span);
            }
            assert(SIZE(topKSpans) <= topk);
            block2spans.insert(make_pair(minimal_block, topKSpans));
            assert(innerP2gs.size() <= topk);

            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            _pit->second.emplace_back(_g);
                        }
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            p2gs[_ipit->first].emplace_back(_g);
                        }
                    }
                    _ipit++;
                }
            }
            if (debug_on) {
                if (!spans.empty()) {
                    printf("[%d]: minimal span size: %zu\n", __LINE__, SIZE(spans));
                    for (int _i = 0; _i < SIZE(spans); _i++) {
                        if (spans[_i][0].second == INT32_MAX) continue;
                        printf("[%d]: minimal time period: %lld, min: %lld, max: %lld, ", __LINE__,
                               spans[_i][1].second - spans[_i][0].second,
                               spans[_i][0].second, spans[_i][1].second);
                        for (int l = 2; l < spans[_i].size(); l++) {
                            auto edge = to_decode_edge(spans[_i][l].first);
                            printf("(%lld, %lld): %lld,", edge.first, edge.second, spans[_i][l].second);
                        }
                        printf("\n");
                    }
                } // end if empty test
            }
        } // end for k-block loop
    }
    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);

    assert(p2gs.size() <= topk);
    // default set top-k = 1
    assert(!p2gs.empty());
//    vector<Graphs> ex_gs;
    vector<vector<pair<long long, long long>>> ans;
//    for (const auto &_g: gs) {
//        Graphs _gs;
//        vector<long long> _nodes;
//        std::transform(_g.nodes.begin(), _g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
//                       [](const Node* _n) -> long long {
//                           return _n->node_id;
//                       });
//        _gs.newGraphsFrom(_nodes, _g);
//        ex_gs.push_back(_gs);
//    }
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    for (const auto &gs: p2gs) {
        for (const auto &g : gs.second) {
            g2rank[g] = 0;
        }
    }
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(g2rank.find(B) != g2rank.end());
            vector<vector<pair<long long, long long>>> spans = block2spans.at(B)[g2rank[B]++];

            if (findTopkVal(ans, topk) < findTopkVal(spans, 1)) {
                continue;
            }
            if (debug_on) printf("%zu %zu\n", community.nodes.size(), community.edges.size());

            // graph expansion init
            B = B.deepCopy();
            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (vistedNodes.size() < community.nodes.size()) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            vector<vector<pair<long long, long long>>> _s;
                            for (const auto &span: spans) {
                                auto exSpans = updateMTCCPeriod(B, span);
                                if (exSpans.empty()) {
                                    set<long long> enlargeRank;
                                    ans.emplace_back(span);
                                    auto enlargeSpans = expandMTCCPeriodNotEmpty(B, span, topk);
                                    unordered_map<long long, vector<vector<pair<long long, long long>>>> _tmp;
                                    for (const auto &elSpan: enlargeSpans) {
                                        enlargeRank.insert(elSpan[1].second - elSpan[0].second);
                                        _tmp[elSpan[1].second - elSpan[0].second].push_back(elSpan);
                                    }
                                    long long _i = 0;
                                    for (const auto &interval: enlargeRank) {
                                        if (_i >= topk) break;
                                        assert(_tmp.find(interval) != _tmp.end());
                                        for (const auto &_span: _tmp.at(interval))
                                            _s.emplace_back(_span);
                                        _i++;
                                    }
                                } else {
                                    for (const auto &ex: exSpans) {
                                        _s.emplace_back(ex);
                                    }
                                }
                            }
                            spans.clear();
                            std::transform(_s.begin(), _s.end(), std::inserter(spans, spans.begin()),
                                           [](const vector<pair<long long, long long>> &v) -> vector<
                                                   pair<long long, long long>> {
                                               return v;
                                           });
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } // end while expansion
            //community-level testing (which means the community is the final subgraph)
            for (const auto &span: spans) ans.emplace_back(span);

        } // end each community
    }   // topk question

    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);
    std::sort(begin(ans), end(ans),
              [](const vector<pair<long long, long long>> &a, const vector<pair<long long, long long>> &b) -> bool {
                  return a.at(1).second - a.at(0).second < b.at(1).second - b.at(0).second;
              });
    long long _recVal = findTopkVal(ans, topk);
    auto iter = ans.rbegin();
    for (; iter != ans.rend(); iter++) {
        if ((*iter)[1].second - (*iter)[0].second == _recVal) break;
    }
    ans.resize(std::distance(iter, ans.rend()));
    return ans;
}


long long findTopkVal(const vector<vector<pair<long long, long long>>> &spans, const long long topk) {
    if (SIZE(spans) < topk) return INT32_MAX;
    auto vals = [&](const vector<vector<pair<long long, long long>>> &spans) -> set<long long> {
        set<long long> vals;
        for (const auto &span: spans) {
            vals.insert(span[1].second - span[0].second);
        }
        return vals;
    }(spans);
    auto iter = vals.begin();
    std::advance(iter, topk - 1);

    return *iter;
}

long long findTopkVal(const vector<pair<long long, long long>> &spans, const long long topk) {
    if (SIZE(spans) < topk) return INT32_MAX;
    auto vals = [&](const vector<pair<long long, long long>> &spans) -> set<long long> {
        set<long long> vals;
        for (const auto &span: spans) {
            vals.insert(span.second - span.first);
        }
        return vals;
    }(spans);
    auto iter = vals.begin();
    std::advance(iter, topk - 1);

    return *iter;
}

bool checkKClique(const Graphs &g) {
    return (SIZE(g.nodes)) * (SIZE(g.nodes) - 1) / 2 == SIZE(g.edges);
}

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCC(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
//    auto deltaTimer = new CUtility();
//    deltaTimer->start();
//    deltaTimer->setFILE(fp);
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
//    deltaTimer->end("delta-community search");
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }

    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<pair<long long, vector<long long>>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> block2info;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, pair<long long, long long>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, pair<long long, long long>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            long long nei_node = neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a;
            bool canAddIn = false;
            for (const auto &_edge: community.id2node.at(nei_node)->connTo) {
                long long back_node = _edge->node_a == nei_node ? _edge->node_b : _edge->node_a;
                if (back_node == query_node) {
                    canAddIn = true;
                    break;
                }
            }
            if (canAddIn) {
                neigh_nodes.emplace_back(nei_node);
            }
        }
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] k_clique_node size: %d\n", __LINE__, SIZE(k_clique_nodes));
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto info = enmuTopkTCCPeriodByOne(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, info);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second;
                            if (c_info.second - c_info.first <= info.second - info.first) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, info);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, pair<long long, long long>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            pair<long long, long long> info = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            community2graphs[community].emplace_back(cand_B);
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
    }
//
    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (!reduction_fast) {
        vector<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = calculateRank(minimal_block);
                if (topk <= info.first) {
                    maxVal.push_back(info.second);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk);
                    maxVal.push_back(calculateRank(minimal_block).second);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        //    timers->end("Max-Min");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        if (debug_info) printf("[%d]: enum global upperbound.\n", __LINE__);
        set<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.insert(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.insert(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        if (debug_info) printf("[%d]: enum global upperbound end.\n", __LINE__);
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    }

    if (debug_info) printf("[%d]:finishing UpperBound calculation\n", __LINE__);
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    block2info.clear();
    community2graphs.clear();
    if (debug_info) printf("Constructing new Graphs\n");
    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node, fp);
    auto *timer = new CUtility();
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
//    auto afterDeltaTimer = new CUtility();
//    afterDeltaTimer->start();
//    afterDeltaTimer->setFILE(fp);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
//    afterDeltaTimer->end("After delta-truss community search.");
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    if (debug_info) {
        printf("[%d]: finishing community search\n", __LINE__);
    }
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, pair<long long, long long>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, pair<long long, long long>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto info = enmuTopkTCCPeriodByOne(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, info);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second;
                            if (c_info.second - c_info.first <= info.second - info.first) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, info);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, pair<long long, long long>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            pair<long long, long long> info = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            auto topkPair = enmuTopkTCCPeriod(cand_B, info, topk);
            vector<vector<pair<long long, vector<long long>>>> spans = topkPair.first;
            vector<pair<long long, long long>> topkinfos = topkPair.second;
            assert(!spans.empty());
            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans.insert(make_pair(cand_B, spans));
            block2info.insert(make_pair(cand_B, topkinfos));

            // 将当前delta基本块 topk放入
            for (const auto &info: topkinfos) {
                innerP2gs[info.second - info.first].emplace_back(cand_B);
            }
            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        _pit->second.emplace_back(_g);
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        p2gs[_ipit->first].emplace_back(_g);
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        p2gs[_ipit->first].emplace_back(_g);
                    }
                    _ipit++;
                }
            }
        } // end-for loop delta-blocks
    }   // end community
    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);

    assert(p2gs.size() <= topk);
    assert(!p2gs.empty());

    // 记录blocks
    deque<BInfo *> BQ; // init
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    vector<pair<Span, Info>> ans;
    unordered_set<vector<pair<long long, vector<long long>>>, VecPairHash<long long>, VecPairComp<long long>> tgRec;
    for (const auto &gs: p2gs)
        for (const auto &g : gs.second)
            g2rank[g] = 0;
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(block2info.find(B) != block2info.end());
            assert(g2rank.find(B) != g2rank.end());
            if (g2rank[B] >= topk) continue;
            vector<pair<long long, vector<long long>>> span = block2spans.at(B)[g2rank[B]];
            pair<long long, long long> info = block2info.at(B)[g2rank[B]];
            g2rank[B]++;

            auto binfo = new BInfo(community, B.deepCopy(), Btruss, span, info, false);
            BQ.emplace_back(binfo);
        }
    }


    long long prev_val = INT32_MIN;
    long long cur_topk = 0;
    while (!BQ.empty()) {
        BInfo *binfo = BQ.front();
        BQ.pop_front();

        // 最小聚集社区
        if (binfo->status) {
            if (prev_val < binfo->info.second - binfo->info.first) {
                prev_val = binfo->info.second - binfo->info.first;
                cur_topk++; // 更新当前topk值
            }
            if (cur_topk > topk) break;
            ans.emplace_back(make_pair(binfo->span, binfo->info));
            continue;
        } else { // 未构成最大聚集社区
            // 获取最新状态
            Graphs community = binfo->community;
            Graphs B = binfo->g;
            bool judgement = false;
            long long curNodeSize = SIZE(B.nodes);
            Truss Btruss = binfo->truss;
            Span span = binfo->span;
            Info info = binfo->info;

            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (SIZE(vistedNodes) < SIZE(community.nodes)) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            auto update_p = updateTopkTCCPeriod(B, span, info, topk);
                            vector<Span> vspan = update_p.first;
                            vector<Info> vinfo = update_p.second;

                            assert(SIZE(vspan) == SIZE(vinfo));
                            for (long long _i = 0; _i < SIZE(vinfo); _i++) {
                                Span u_span = vspan.at(_i);
                                Info u_info = vinfo.at(_i);
                                if (_i == 0) {
                                    if (!(u_info.first == info.first && u_info.second == info.second)) {
                                        if (tgRec.find(span) == tgRec.end()) {
                                            tgRec.insert(span);
                                            Graphs _;
                                            Truss __;
                                            auto oribinfo = new BInfo(_, _, __, span, info, true);
                                            BQ.emplace_back(oribinfo);
                                            auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                      false);
                                            BQ.emplace_back(newbinfo);
                                            judgement = true;
                                            goto L1;
                                        }
                                    } else {
                                        auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                  false);
                                        BQ.emplace_back(newbinfo);

                                        goto L1;
                                    }
                                } else {
                                    auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info, false);
                                    BQ.emplace_back(newbinfo);

                                    goto L1;
                                }
                            }
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } //End 子图扩展
            // 最大扩展至社区规模
            L1:
            if (curNodeSize != SIZE(community.nodes) && SIZE(vistedNodes) == SIZE(community.nodes)) {
                Graphs _;
                Truss __;
                auto oribinfo = new BInfo(_, _, __, span, info, true);
                BQ.emplace_back(oribinfo);
            }
        }

        // 按聚集社区长度重新排序
        std::sort(BQ.begin(), BQ.end(), [](const BInfo *a, const BInfo *b) -> bool {
            return a->info.second - a->info.first < b->info.second - b->info.first;
        });
    }
    return ans;
}

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
enmuTopkTCCPeriodNotOptiz(const Graphs &g, const pair<long long, long long> &info, const long long topk) {
    vector<vector<pair<long long, vector<long long>>>> container; // path
    vector<pair<long long, long long>> infos;  // info
    // info.first: min, info.second: max.

    vector<pair<long long, vector<long long>>> init_length;
    for (int _i = 0; _i < SIZE(g.edges); ++_i) {
        Edge *edge = g.edges.at(_i);
        vector<long long> ocs;
        for (const auto &oc: edge->occur) {
            if (oc >= info.first && oc <= info.second) {
                ocs.emplace_back(oc);
            }
        }
        init_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
    }
    container.emplace_back(init_length);
    infos.emplace_back(info);
    if (topk > 1) {
        vector<pair<long long, long long>> topkMaintainInfo(topk - 1);
        for (int _i = 0; _i < SIZE(g.edges); ++_i) {
            Edge *edge = g.edges.at(_i);
            vector<pair<long long, long long>> innerInfos;
            if (_i == 0) {
                unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
                for (const auto &oc: edge->occur) {
                    long long minVal = std::min(info.first, oc);
                    long long maxVal = std::max(info.second, oc);
                    if (rec.find(make_pair(minVal, maxVal)) == rec.end()) {
                        innerInfos.emplace_back(make_pair(minVal, maxVal));
                        rec.insert(make_pair(minVal, maxVal));
                    }
                }

                topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
            } else {
                unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
                for (const auto &oc: edge->occur) {
                    for (const auto &candInfo: topkMaintainInfo) {
                        long long minVal = std::min(candInfo.first, oc);
                        long long maxVal = std::max(candInfo.second, oc);
                        auto cur_pair = make_pair(minVal, maxVal);
                        if (rec.find(cur_pair) == rec.end()) {
                            innerInfos.emplace_back(cur_pair);
                            rec.insert(cur_pair);
                        }
                    }
                }
                topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
            }
        } // end for-loop edegs
        assert(SIZE(topkMaintainInfo) >= 1);
        std::sort(begin(topkMaintainInfo), end(topkMaintainInfo),
                  [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                      return a.second - a.first < b.second - b.first;
                  });
        if (topkMaintainInfo[0].second - topkMaintainInfo[0].first > info.second - info.first) {
            topkMaintainInfo.resize(topk - 1);
        } else {
            topkMaintainInfo.resize(topk);
            topkMaintainInfo.erase(topkMaintainInfo.begin());
        }
        for (const auto &topkInfo: topkMaintainInfo)
            infos.emplace_back(topkInfo);
    }   // end-if topk==1


    for (long long _i = 1; _i < SIZE(infos); _i++) {
        auto prev = infos[_i - 1];
        auto cur = infos[_i];
        vector<pair<long long, vector<long long>>> topk_length;
        for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
            Edge *edge = g.edges.at(_ei);
            vector<long long> ocs;
            for (const auto &oc: edge->occur) {
//                if (oc < prev.first && oc >= cur.first && oc > prev.second && oc <= cur.second) {
                if (oc >= cur.first && oc <= cur.second) {
                    ocs.emplace_back(oc);
                }
            }
            topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
        }
        container.emplace_back(topk_length);
    }

    assert(SIZE(container) == SIZE(infos));
    assert(SIZE(container) <= topk);
    return make_pair(container, infos);
}

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
enmuTopkTCCPeriod(const Graphs &g, const pair<long long, long long> &info, const long long topk) {
    vector<vector<pair<long long, vector<long long>>>> container; // path
    vector<pair<long long, long long>> infos;  // info
    // info.first: min, info.second: max.

    vector<pair<long long, vector<long long>>> init_length;
    for (int _i = 0; _i < SIZE(g.edges); ++_i) {
        Edge *edge = g.edges.at(_i);
        vector<long long> ocs;
        for (const auto &oc: edge->occur) {
            if (oc >= info.first && oc <= info.second) {
                ocs.emplace_back(oc);
            }
        }
        init_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
    }
    container.emplace_back(init_length);
    infos.emplace_back(info);

    if (topk > 1) {
        vector<pair<long long, long long>> topkMaintainInfo(topk - 1);
        for (int _i = 0; _i < SIZE(g.edges); ++_i) {
            Edge *edge = g.edges.at(_i);
            vector<pair<long long, long long>> innerInfos;
            if (_i == 0) {
                unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
                for (const auto &oc: edge->occur) {
                    long long minVal = std::min(info.first, oc);
                    long long maxVal = std::max(info.second, oc);
                    if (rec.find(make_pair(minVal, maxVal)) == rec.end()) {
                        innerInfos.emplace_back(make_pair(minVal, maxVal));
                        rec.insert(make_pair(minVal, maxVal));
                    }
                }

                if (SIZE(innerInfos) > topk - 1) {
                    std::sort(begin(innerInfos), end(innerInfos),
                              [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                                  return a.second - a.first < b.second - b.first;
                              });
                    innerInfos.resize(topk - 1);
                }
                topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
            } else {
                unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
                for (const auto &oc: edge->occur) {
                    for (const auto &candInfo: topkMaintainInfo) {
                        long long minVal = std::min(candInfo.first, oc);
                        long long maxVal = std::max(candInfo.second, oc);
                        auto cur_pair = make_pair(minVal, maxVal);
                        if (rec.find(cur_pair) == rec.end()) {
                            innerInfos.emplace_back(cur_pair);
                            rec.insert(cur_pair);
                        }
                    }
                }

                if (SIZE(innerInfos) > topk - 1) {
                    std::sort(begin(innerInfos), end(innerInfos),
                              [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                                  return a.second - a.first < b.second - b.first;
                              });
                    if (innerInfos[0].second - innerInfos[0].first > info.second - info.first) {
                        innerInfos.resize(topk - 1);
                    } else {
                        innerInfos.resize(topk);
                        innerInfos.erase(innerInfos.begin());
                    }
                }
                topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
            }
        } // end for-loop edegs
        assert(SIZE(topkMaintainInfo) >= 1);
        for (const auto &topkInfo: topkMaintainInfo)
            infos.emplace_back(topkInfo);
    }   // end-if topk==1

    for (long long _i = 1; _i < SIZE(infos); _i++) {
        auto prev = infos[_i - 1];
        auto cur = infos[_i];
        vector<pair<long long, vector<long long>>> topk_length;
        for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
            Edge *edge = g.edges.at(_ei);
            vector<long long> ocs;
            for (const auto &oc: edge->occur) {
//                if (oc < prev.first && oc >= cur.first && oc > prev.second && oc <= cur.second) {
                if (oc >= cur.first && oc <= cur.second) {
                    ocs.emplace_back(oc);
                }
            }
            topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
        }
        container.emplace_back(topk_length);
    }

    assert(SIZE(container) == SIZE(infos));
    assert(SIZE(container) <= topk);
    return make_pair(container, infos);
}

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
updateTopkTCCPeriodNoOptiz(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                           const pair<long long, long long> &info, const long long topk) {
    vector<vector<pair<long long, vector<long long>>>> container; // path
    vector<pair<long long, long long>> infos;  // info
    // info.first: min, info.second: max.

    assert(topk >= 1);

    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;

    for (int _pi = 0; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge), edge));
        }
    }
    vector<pair<long long, Edge *>> vnewRestEdges(begin(newRestEdges), end(newRestEdges));


    vector<pair<long long, long long>> topkMaintainInfo;
    for (int _i = 0; _i < SIZE(vnewRestEdges); ++_i) {
        Edge *edge = vnewRestEdges.at(_i).second;
        vector<pair<long long, long long>> innerInfos;
        if (_i == 0) {
            for (const auto &oc: edge->occur) {
                long long minVal = std::min(info.first, oc);
                long long maxVal = std::max(info.second, oc);
                innerInfos.emplace_back(make_pair(minVal, maxVal));
            }

            topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
        } else {
            unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
            for (const auto &oc: edge->occur) {
                for (const auto &candInfo: topkMaintainInfo) {
                    long long minVal = std::min(candInfo.first, oc);
                    long long maxVal = std::max(candInfo.second, oc);
                    auto cur_pair = make_pair(minVal, maxVal);
                    if (rec.find(cur_pair) == rec.end()) {
                        innerInfos.emplace_back(cur_pair);
                        rec.insert(cur_pair);
                    }
                }
            }
            topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
        }
    } // end for-loop edegs
    std::sort(begin(topkMaintainInfo), end(topkMaintainInfo),
              [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                  return a.second - a.first < b.second - b.first;
              });
    for (const auto &topkInfo: topkMaintainInfo)
        infos.emplace_back(topkInfo);

    long long curK = SIZE(infos);
    if (curK > topk) {
        infos.resize(topk);
    } else {
        infos.resize(curK);
    }
    for (long long _i = 0; _i < SIZE(infos); _i++) {
        auto cur = infos[_i];
        vector<pair<long long, vector<long long>>> topk_length;
        if (_i == 0) {
//            for (int _ei = 0; _ei < SIZE(vnewRestEdges); ++_ei) {
            for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
                Edge *edge = g.edges.at(_ei);
//                Edge *edge = vnewRestEdges.at(_ei).second;
                vector<long long> ocs;
                for (const auto &oc: edge->occur) {
                    if (oc >= cur.first && oc <= cur.second) {
                        ocs.emplace_back(oc);
                    }
                }
                topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
            }
        } else {
            auto prev = infos[_i - 1];
//            for (int _ei = 0; _ei < SIZE(vnewRestEdges); ++_ei) {
            for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
//                Edge *edge = vnewRestEdges.at(_ei).second;
                Edge *edge = g.edges.at(_ei);
                vector<long long> ocs;
                for (const auto &oc: edge->occur) {
//                    if (oc < prev.first && oc >= cur.first && oc > prev.second && oc <= cur.second) {
                    if (oc >= cur.first && oc <= cur.second) {
                        ocs.emplace_back(oc);
                    }
                }
                topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
            }
        }
        container.emplace_back(topk_length);
    }

    assert(SIZE(container) == SIZE(infos));
    assert(SIZE(container) <= topk);
    return make_pair(container, infos);
}

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
updateTopkTCCPeriod(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                    const pair<long long, long long> &info, const long long topk) {
    vector<vector<pair<long long, vector<long long>>>> container; // path
    vector<pair<long long, long long>> infos;  // info
    // info.first: min, info.second: max.

    assert(topk >= 1);

    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;

    for (int _pi = 0; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge), edge));
        }
    }
    vector<pair<long long, Edge *>> vnewRestEdges(begin(newRestEdges), end(newRestEdges));


    vector<pair<long long, long long>> topkMaintainInfo(topk);
    for (int _i = 0; _i < SIZE(vnewRestEdges); ++_i) {
        Edge *edge = vnewRestEdges.at(_i).second;
        vector<pair<long long, long long>> innerInfos;
        if (_i == 0) {
            for (const auto &oc: edge->occur) {
                long long minVal = std::min(info.first, oc);
                long long maxVal = std::max(info.second, oc);
                innerInfos.emplace_back(make_pair(minVal, maxVal));
            }

            if (SIZE(innerInfos) > topk) {
                std::sort(begin(innerInfos), end(innerInfos),
                          [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                              return a.second - a.first < b.second - b.first;
                          });
                innerInfos.resize(topk);
            }
            topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
        } else {
            unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
            for (const auto &oc: edge->occur) {
                for (const auto &candInfo: topkMaintainInfo) {
                    long long minVal = std::min(candInfo.first, oc);
                    long long maxVal = std::max(candInfo.second, oc);
                    auto cur_pair = make_pair(minVal, maxVal);
                    if (rec.find(cur_pair) == rec.end()) {
                        innerInfos.emplace_back(cur_pair);
                        rec.insert(cur_pair);
                    }
                }
            }

            if (SIZE(innerInfos) > topk) {
                std::sort(begin(innerInfos), end(innerInfos),
                          [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                              return a.second - a.first < b.second - b.first;
                          });
                innerInfos.resize(topk);
            }
            topkMaintainInfo.assign(begin(innerInfos), end(innerInfos));
        }
    } // end for-loop edegs
    for (const auto &topkInfo: topkMaintainInfo)
        infos.emplace_back(topkInfo);


    for (long long _i = 0; _i < SIZE(infos); _i++) {
        auto cur = infos[_i];
        vector<pair<long long, vector<long long>>> topk_length;
        if (_i == 0) {
            for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
                Edge *edge = g.edges.at(_ei);
                vector<long long> ocs;
                for (const auto &oc: edge->occur) {
                    if (oc >= cur.first && oc <= cur.second) {
                        ocs.emplace_back(oc);
                    }
                }
                topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
            }
        } else {
            auto prev = infos[_i - 1];
            for (int _ei = 0; _ei < SIZE(g.edges); ++_ei) {
                Edge *edge = g.edges.at(_ei);
                vector<long long> ocs;
                for (const auto &oc: edge->occur) {
//                    if (oc < prev.first && oc >= cur.first && oc > prev.second && oc <= cur.second) {
                    if (oc >= cur.first && oc <= cur.second) {
                        ocs.emplace_back(oc);
                    }
                }
                topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
            }
        }
        container.emplace_back(topk_length);
    }

    assert(SIZE(container) == SIZE(infos));
    assert(SIZE(container) <= topk);
    return make_pair(container, infos);
}


pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>
updateTopkTCCPeriodByOne(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                         const pair<long long, long long> &info) {

    unordered_set<long long> edges;
    unordered_map<long long, Edge *> newRestEdges;

    for (int _pi = 0; _pi < SIZE(span); ++_pi) {
        auto _p = span.at(_pi);
        edges.insert(_p.first);
    }

    for (const auto &edge: g.edges) {
        if (edges.find(to_encode_edge(edge)) == edges.end()) {
            newRestEdges.insert(make_pair(to_encode_edge(edge), edge));
        }
    }
    vector<pair<long long, Edge *>> vnewRestEdges(begin(newRestEdges), end(newRestEdges));


    pair<long long, long long> topkMaintainInfo;
    for (int _i = 0; _i < SIZE(vnewRestEdges); ++_i) {
        Edge *edge = vnewRestEdges.at(_i).second;
        vector<pair<long long, long long>> innerInfos;
        if (_i == 0) {
            for (const auto &oc: edge->occur) {
                long long minVal = std::min(info.first, oc);
                long long maxVal = std::max(info.second, oc);
                innerInfos.emplace_back(make_pair(minVal, maxVal));
            }

            if (SIZE(innerInfos) > 1) {
                std::sort(begin(innerInfos), end(innerInfos),
                          [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                              return a.second - a.first < b.second - b.first;
                          });
                innerInfos.resize(1);
            }
            topkMaintainInfo = innerInfos.at(0);
        } else {
            unordered_set<pair<long long, long long>, PairHash<long long>, PairComp<long long>> rec;
            for (const auto &oc: edge->occur) {
                long long minVal = std::min(topkMaintainInfo.first, oc);
                long long maxVal = std::max(topkMaintainInfo.second, oc);
                auto cur_pair = make_pair(minVal, maxVal);
                if (rec.find(cur_pair) == rec.end()) {
                    innerInfos.emplace_back(cur_pair);
                    rec.insert(cur_pair);
                }
            }

            if (SIZE(innerInfos) > 1) {
                std::sort(begin(innerInfos), end(innerInfos),
                          [&](const pair<long long, long long> &a, const pair<long long, long long> &b) -> bool {
                              return a.second - a.first < b.second - b.first;
                          });
                innerInfos.resize(1);
            }
            topkMaintainInfo = innerInfos.at(0);
        }
    } // end for-loop edegs


    vector<pair<long long, vector<long long>>> topk_length;
    for (int _ei = 0; _ei < SIZE(vnewRestEdges); ++_ei) {
        Edge *edge = vnewRestEdges.at(_ei).second;
        vector<long long> ocs;
        for (const auto &oc: edge->occur) {
            if (oc < info.first && oc >= topkMaintainInfo.first && oc <= topkMaintainInfo.second && oc > info.second) {
                ocs.emplace_back(oc);
            }
        }
        topk_length.emplace_back(make_pair(to_encode_edge(edge), ocs));
    }
    for (const auto &_span: span) topk_length.emplace_back(_span);

    return make_pair(topk_length, topkMaintainInfo);
}

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
BackUp(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast) {
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }

    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<pair<long long, vector<long long>>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> block2info;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, pair<long long, long long>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, pair<long long, long long>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            long long nei_node = neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a;
            bool canAddIn = false;
            for (const auto &_edge: community.id2node.at(nei_node)->connTo) {
                long long back_node = _edge->node_a == nei_node ? _edge->node_b : _edge->node_a;
                if (back_node == query_node) {
                    canAddIn = true;
                    break;
                }
            }
            if (canAddIn) {
                neigh_nodes.emplace_back(nei_node);
            }
        }
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] k_clique_node size: %d\n", __LINE__, SIZE(k_clique_nodes));
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto info = enmuTopkTCCPeriodByOne(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, info);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second;
                            if (c_info.second - c_info.first <= info.second - info.first) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, info);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, pair<long long, long long>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            pair<long long, long long> info = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            community2graphs[community].emplace_back(cand_B);
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
    }
//
    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (!reduction_fast) {
        vector<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = calculateRank(minimal_block);
                if (topk <= info.first) {
                    maxVal.push_back(info.second);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk);
                    maxVal.push_back(calculateRank(minimal_block).second);
                }
            }
        }
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        //    timers->end("Max-Min");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        //    timers->start();
        if (debug_info) printf("[%d]: enum global upperbound.\n", __LINE__);
        set<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.insert(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.insert(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        if (debug_info) printf("[%d]: enum global upperbound end.\n", __LINE__);
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
//        timers->end("Topk-Retrival");
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    }

    if (debug_info) printf("[%d]:finishing UpperBound calculation\n", __LINE__);
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    block2info.clear();
    community2graphs.clear();
    if (debug_info) printf("Constructing new Graphs\n");
    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node);
    auto *timer = new CUtility();
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }

    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    if (debug_info) {
        printf("[%d]: finishing community search\n", __LINE__);
    }
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, pair<long long, long long>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, pair<long long, long long>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto info = enmuTopkTCCPeriodByOne(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, info);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second;
                            if (c_info.second - c_info.first <= info.second - info.first) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, info);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, pair<long long, long long>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            pair<long long, long long> info = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            auto topkPair = enmuTopkTCCPeriod(cand_B, info, topk);
            vector<vector<pair<long long, vector<long long>>>> spans = topkPair.first;
            vector<pair<long long, long long>> topkinfos = topkPair.second;
            assert(!spans.empty());
            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans.insert(make_pair(cand_B, spans));
            block2info.insert(make_pair(cand_B, topkinfos));

            // 将当前delta基本块 topk放入
            for (const auto &info: topkinfos) {
                innerP2gs[info.second - info.first].emplace_back(cand_B);
            }
            auto _pit = p2gs.begin();
            auto _ipit = innerP2gs.begin();
            while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                if (_pit->first < _ipit->first) _pit++;
                else if (_pit->first == _ipit->first) {
                    for (const auto &_g: _ipit->second) {
                        _pit->second.emplace_back(_g);
                    }
                    _pit++, _ipit++;
                } else {
                    if (SIZE(p2gs) == topk) {
                        auto _iter = p2gs.begin();
                        std::advance(_iter, SIZE(p2gs) - 1);
                        _pit = p2gs.erase(_iter);
                    }
                    for (const auto &_g: _ipit->second) {
                        p2gs[_ipit->first].emplace_back(_g);
                    }
                    _ipit++;
                }
            }
            if (SIZE(p2gs) < topk) {
                while (_ipit != innerP2gs.end()) {
                    for (const auto &_g: _ipit->second) {
                        p2gs[_ipit->first].emplace_back(_g);
                    }
                    _ipit++;
                }
            }
        } // end-for loop delta-blocks
    }   // end community
    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);

    assert(p2gs.size() <= topk);
    assert(!p2gs.empty());

    vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>> ans;
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    for (const auto &gs: p2gs)
        for (const auto &g : gs.second)
            g2rank[g] = 0;
    unordered_set<vector<pair<long long, vector<long long>>>, VecPairHash<long long>, VecPairComp<long long>> tgRec;
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(block2info.find(B) != block2info.end());
            assert(g2rank.find(B) != g2rank.end());
            if (g2rank[B] >= topk) continue;
            vector<pair<long long, vector<long long>>> span = block2spans.at(B)[g2rank[B]];
            pair<long long, long long> info = block2info.at(B)[g2rank[B]];
            g2rank[B]++;
            // graph expansion init
            B = B.deepCopy();
            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (SIZE(vistedNodes) < SIZE(community.nodes)) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            vector<vector<pair<long long, long long>>> _s;
                            auto update_p = updateTopkTCCPeriodByOne(B, span, info);
                            vector<pair<long long, vector<long long>>> u_span = update_p.first;
                            pair<long long, long long> u_info = update_p.second;
                            if (!(u_info.first == info.first && u_info.second == info.second)) {
                                if (tgRec.find(span) == tgRec.end()) {
                                    ans.emplace_back(make_pair(span, info));
                                    tgRec.insert(span);
                                }
                            }
                            span = u_span;
                            info = u_info;
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } // end while expansion
            //community-level testing (which means the community is the final subgraph)
            ans.emplace_back(make_pair(span, info));

        } // end each community
    }   // topk question

    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);
    std::sort(begin(ans), end(ans),
              [](const pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>> &a,
                 const pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>> &b) -> bool {
                  return a.second.second - a.second.first < b.second.second - b.second.first;
              });
    vector<pair<long long, long long>> info_;
    for (const auto &_ans: ans) info_.emplace_back(_ans.second);
    long long _recVal = findTopkVal(info_, topk);
    auto iter = info_.rbegin();
    for (; iter != info_.rend(); iter++) {
        if ((*iter).second - (*iter).first == _recVal) break;
    }
    ans.resize(std::distance(iter, info_.rend()));
    return ans;
}

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCCS(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast) {
    auto starter = new CUtility();
    starter->setFILE(fp);
    starter->start();
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
    auto deltaTimer = new CUtility();
    deltaTimer->start();
    deltaTimer->setFILE(fp);
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    deltaTimer->end("delta-community search");
    for (const auto &c: communities) {
        ct_density(c);
    }
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<vector<pair<long long, vector<long long>>>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<vector<pair<long long, long long>>>, GraphsHash, GraphsComp> block2info;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        detect_shortest_length(community);
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, vector<pair<long long, long long>>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, vector<pair<long long, long long>>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto infos = enmuTopkTCCPeriodEqual(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                assert(SIZE(infos) > 0);
                long long interval = infos.at(0).second - infos.at(0).first;
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, infos);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second.at(0);
                            if (c_info.second - c_info.first <= interval) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, infos);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            vector<pair<long long, long long>> infos = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans[cand_B].resize(topk);
            block2info[cand_B].resize(topk);
            community2graphs[community].emplace_back(cand_B);
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
    }
    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (reduction_fast) {
        if (debug_info) printf("[%d]: enum global upperbound.\n", __LINE__);
        set<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.insert(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.insert(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        if (debug_info) printf("[%d]: enum global upperbound end.\n", __LINE__);
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        upperBound = INT32_MAX;
    }

    if (debug_info) printf("[%d]:finishing UpperBound calculation\n", __LINE__);
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    block2info.clear();
    community2graphs.clear();
    if (debug_info) printf("Constructing new Graphs\n");
    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node, fp);
    starter->end("End Construction");
    auto *timer = new CUtility();
    timer->setFILE(fp);
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    auto afterDeltaTimer = new CUtility();
    afterDeltaTimer->start();
    afterDeltaTimer->setFILE(fp);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
    afterDeltaTimer->end("After delta-truss community search.");
    return vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>();
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    if (debug_info) {
        printf("[%d]: finishing community search\n", __LINE__);
    }
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, vector<pair<long long, long long>>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, vector<pair<long long, long long>>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto infos = enmuTopkTCCPeriodEqual(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                assert(SIZE(infos) > 0);
                long long interval = infos.at(0).second - infos.at(0).first;
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, infos);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second.at(0);
                            if (c_info.second - c_info.first <= interval) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, infos);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            vector<pair<long long, long long>> infos = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans[cand_B].resize(topk);
            block2info[cand_B].resize(topk);
            for (const auto &each_info: infos) {
                auto topkPair = enmuTopkTCCPeriod(cand_B, each_info, topk);
                vector<vector<pair<long long, vector<long long>>>> spans = topkPair.first;
                vector<pair<long long, long long>> topkinfos = topkPair.second;
                assert(!spans.empty());
                assert(SIZE(spans) <= topk);
                assert(SIZE(topkinfos) <= topk);
                for (long long _topi = 0; _topi < SIZE(spans); _topi++) {
                    block2spans[cand_B][_topi].emplace_back(spans.at(_topi));
                }
                for (long long _topi = 0; _topi < SIZE(topkinfos); _topi++) {
                    block2info[cand_B][_topi].emplace_back(topkinfos.at(_topi));
                }
                // 将当前delta基本块 topk放入
                for (const auto &info: topkinfos) {
                    if (innerP2gs.find(info.second - info.first) == innerP2gs.end()) {
                        innerP2gs[info.second - info.first].emplace_back(cand_B);
                    } else {
                        auto interval = info.second - info.first;
                        if (std::find(innerP2gs[interval].begin(), innerP2gs[interval].end(), cand_B) ==
                            innerP2gs[interval].end()) {
                            innerP2gs[interval].emplace_back(cand_B);
                        }
                    }
                }
                auto _pit = p2gs.begin();
                auto _ipit = innerP2gs.begin();
                while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                    if (_pit->first < _ipit->first) _pit++;
                    else if (_pit->first == _ipit->first) {
                        for (const auto &_g: _ipit->second) {
                            if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                                _pit->second.emplace_back(_g);
                            }
                        }
                        _pit++, _ipit++;
                    } else {
                        if (SIZE(p2gs) == topk) {
                            auto _iter = p2gs.begin();
                            std::advance(_iter, SIZE(p2gs) - 1);
                            _pit = p2gs.erase(_iter);
                        }
                        for (const auto &_g: _ipit->second) {
//                            if (std::find(_ipit->second.begin(), _ipit->second.end(), _g) == _ipit->second.end()) {
                            if (std::find(p2gs[_ipit->first].begin(), p2gs[_ipit->first].end(), _g) ==
                                p2gs[_ipit->first].end()) {
                                p2gs[_ipit->first].emplace_back(_g);
                            }
                        }
                        _ipit++;
                    }
                }
                if (SIZE(p2gs) < topk) {
                    while (_ipit != innerP2gs.end()) {
                        for (const auto &_g: _ipit->second) {
//                            if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            if (std::find(p2gs[_ipit->first].begin(), p2gs[_ipit->first].end(), _g) ==
                                p2gs[_ipit->first].end()) {
                                p2gs[_ipit->first].emplace_back(_g);
                            }
                        }
                        _ipit++;
                    }
                }
            } // end each info
        } // end-for loop delta-blocks
    }   // end community
    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);

    assert(p2gs.size() <= topk);
    assert(!p2gs.empty());
    // 记录blocks
    deque<BInfo *> BQ; // init
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    vector<pair<Span, Info>> ans;
    unordered_set<vector<pair<long long, vector<long long>>>, VecPairHash<long long>, VecPairComp<long long>> tgRec;
    for (const auto &gs: p2gs)
        for (const auto &g : gs.second)
            g2rank[g] = 0;
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(block2info.find(B) != block2info.end());
            assert(g2rank.find(B) != g2rank.end());
            if (g2rank[B] >= topk) continue;
            vector<vector<pair<long long, vector<long long>>>> t_spans = block2spans.at(B)[g2rank[B]];
            vector<pair<long long, long long>> t_infos = block2info.at(B)[g2rank[B]];
            g2rank[B]++;
            assert(SIZE(t_infos) == SIZE(t_infos));
            for (long long _ti = 0; _ti < SIZE(t_infos); _ti++) {
                auto binfo = new BInfo(community, B.deepCopy(), Btruss, t_spans.at(_ti), t_infos.at(_ti), false);
                BQ.emplace_back(binfo);
            }
        }
    }

    // 按聚集社区长度重新排序
    std::sort(BQ.begin(), BQ.end(), [](const BInfo *a, const BInfo *b) -> bool {
        return a->info.second - a->info.first < b->info.second - b->info.first;
    });
    timer->end("Starting calculating (Before BQ)");
    int k_rec[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 20, 25, 30, 50, 100};
    unordered_set<int> ku_rec(begin(k_rec), end(k_rec));
    timer->start();
    long long prev_val = INT32_MIN;
    long long cur_topk = 0;
    while (!BQ.empty()) {
        BInfo *binfo = BQ.front();
        BQ.pop_front();
        // 最小聚集社区
        if (binfo->status) {
            if (prev_val < binfo->info.second - binfo->info.first) {
                prev_val = binfo->info.second - binfo->info.first;
                cur_topk++; // 更新当前topk值
            }
            if (cur_topk > topk) break;
            if (ku_rec.find(cur_topk) != ku_rec.end()) {
                timer->end("end with top-" + to_string(cur_topk));
                timer->start();
            }
            ans.emplace_back(make_pair(binfo->span, binfo->info));
            continue;
        } else { // 未构成最大聚集社区
            // 获取最新状态
            Graphs community = binfo->community;
            Graphs B = binfo->g;
            long long curNodeSize = SIZE(B.nodes);
            bool judgement = false;
            Truss Btruss = binfo->truss;
            Span span = binfo->span;
            Info info = binfo->info;

            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (SIZE(vistedNodes) < SIZE(community.nodes)) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            auto update_p = updateTopkTCCPeriod(B, span, info, topk);
                            vector<Span> vspan = update_p.first;
                            vector<Info> vinfo = update_p.second;

                            assert(SIZE(vspan) == SIZE(vinfo));
                            for (long long _i = 0; _i < SIZE(vinfo); _i++) {
                                Span u_span = vspan.at(_i);
                                Info u_info = vinfo.at(_i);
                                if (_i == 0) {
                                    if (!(u_info.first == info.first && u_info.second == info.second)) {
                                        if (tgRec.find(span) == tgRec.end()) {
                                            tgRec.insert(span);
                                            Graphs _;
                                            Truss __;
                                            auto oribinfo = new BInfo(_, _, __, span, info, true);
                                            BQ.emplace_back(oribinfo);
                                            auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                      false);
                                            BQ.emplace_back(newbinfo);
                                            judgement = true;

                                            goto L1;
                                        }
                                    } else {
                                        auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                  false);
                                        BQ.emplace_back(newbinfo);

                                        goto L1;
                                    }
                                } else {
                                    auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info, false);
                                    BQ.emplace_back(newbinfo);

                                    goto L1;
                                }
                            }
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } //End 子图扩展
            // 最大扩展至社区规模
            L1:
            if (!judgement && SIZE(vistedNodes) == SIZE(community.nodes)) {
                Graphs _;
                Truss __;
                auto oribinfo = new BInfo(_, _, __, span, info, true);
                BQ.emplace_back(oribinfo);
            }
        }

        // 按聚集社区长度重新排序
        std::sort(BQ.begin(), BQ.end(), [](const BInfo *a, const BInfo *b) -> bool {
            return a->info.second - a->info.first < b->info.second - b->info.first;
        });
    }
    timer->end("FASTTCCS COST");
    return ans;
}

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCCS_L(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast) {
    auto starter = new CUtility();
    starter->setFILE(fp);
    starter->start();
    Truss truss;
    for (auto &edge: g.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    long long max_truss = truss_decomposition(g, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
    // verification
//    Truss ver_truss;
//    long long ver_max_truss = truss_decomposition(graph, ver_truss);
//    printf("ver max truss is: %d\n", ver_max_truss);
    /*
     * baseline: fixed time step calculation
     */
    long long k = _k;    // k-truss
    long long query_node = _query_node;
//    auto deltaTimer = new CUtility();
//    deltaTimer->start();
//    deltaTimer->setFILE(fp);
    vector<Graphs> communities = baseline_community_search_with_truss(g, truss, k, query_node);
    for (const auto &c: communities) {
        ct_density(c);
    }
//    deltaTimer->end("delta-community search");
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    /*
     * top-k time-coherent community search.
     */
    long long topk = _topk;
    map<long long, vector<Graphs>> p2gs;
    unordered_map<Graphs, Graphs, GraphsHash, GraphsComp> block2community;
    unordered_map<Graphs, Truss, GraphsHash, GraphsComp> block2truss;
    unordered_map<Graphs, vector<vector<vector<pair<long long, vector<long long>>>>>, GraphsHash, GraphsComp> block2spans;
    unordered_map<Graphs, vector<vector<pair<long long, long long>>>, GraphsHash, GraphsComp> block2info;
    unordered_map<Graphs, vector<Graphs>, GraphsHash, GraphsComp> community2graphs;
    /*
     * Upper Bound Calculation
     */
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, vector<pair<long long, long long>>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, vector<pair<long long, long long>>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto infos = enmuTopkTCCPeriodEqual(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                assert(SIZE(infos) > 0);
                long long interval = infos.at(0).second - infos.at(0).first;
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, infos);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second.at(0);
                            if (c_info.second - c_info.first <= interval) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, infos);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            vector<pair<long long, long long>> infos = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans[cand_B].resize(topk);
            block2info[cand_B].resize(topk);
            community2graphs[community].emplace_back(cand_B);
        }
//        printf("find %lld-clique with query node %lld: %zu\n", k, query_node, cand_k_clique_nodes.size());
    }
    long long upperBound = -1;
//    auto timers = new CUtility();
//    timers->start();
    if (reduction_fast) {
        if (debug_info) printf("[%d]: enum global upperbound.\n", __LINE__);
        set<long long> maxVal;
        for (const auto &community: communities) {
            auto it = community2graphs.begin()->first;
            assert(community2graphs.find(community) != community2graphs.end());
            for (auto &minimal_block: community2graphs.at(community)) {
                Truss minimalTruss = block2truss.at(minimal_block);
                auto info = reCalculateRank(minimal_block, topk);
                if (topk <= info.first) {
                    maxVal.insert(info.second[topk - 1]);
                } else {
                    graphExpansion(minimal_block, minimalTruss, community, k, topk, true);
                    auto rank = reCalculateRank(minimal_block, topk).second;
                    maxVal.insert(SIZE(rank) <= topk ? rank[SIZE(rank) - 1] : rank[topk - 1]);
                }
            }
        }
        if (debug_info) printf("[%d]: enum global upperbound end.\n", __LINE__);
        upperBound = *std::min_element(begin(maxVal), end(maxVal));
        if (debug_on)
            printf("[%d]: Upper Bound %lld\n", __LINE__, upperBound);
    } else {
        upperBound = INT32_MAX;
    }

    if (debug_info) printf("[%d]:finishing UpperBound calculation\n", __LINE__);
//    long long debug;
//    cin >> debug;
    /*
     * Graph Reduction
     */
    truss.clear();
    communities.clear();
    p2gs.clear();
    block2community.clear();
    block2truss.clear();
    block2spans.clear();
    block2info.clear();
    community2graphs.clear();
    if (debug_info) printf("Constructing new Graphs\n");
    Graphs gUb;
    vector<long long> _nodes;
    std::transform(g.nodes.begin(), g.nodes.end(), std::inserter(_nodes, _nodes.begin()),
                   [](const Node *_n) -> long long {
                       return _n->node_id;
                   });
    gUb.newGraphsFrom(_nodes, g);
    // new graph: gUb
    updateGraphByUpperBound(gUb, upperBound, query_node, fp);
    starter->end("End Construction");
    auto *timer = new CUtility();
    timer->setFILE(fp);
    timer->start();

    for (auto &edge: gUb.edges) {
        std::sort(begin(edge->occur), end(edge->occur));
    }
    std::sort(begin(g.edges), end(g.edges), [](const Edge *a, const Edge *b) -> bool {
        return SIZE(a->occur) < SIZE(b->occur);
    });
    max_truss = truss_decomposition(gUb, truss);
    if (debug_on) printf("[%d]: max truss is: %lld\n", __LINE__, max_truss);
//    auto afterDeltaTimer = new CUtility();
//    afterDeltaTimer->start();
//    afterDeltaTimer->setFILE(fp);
    communities = baseline_community_search_with_truss(gUb, truss, k, query_node);
//    afterDeltaTimer->end("After delta-truss community search.");
    assert(!communities.empty());
    if (debug_on) {
        printf("[%d]: Found communities %zu under k=%lld, query node: %lld, node size: %zu.\n", __LINE__,
               communities.size(), k,
               query_node,
               communities[0].nodes.size());
    }
    if (debug_info) {
        printf("[%d]: finishing community search\n", __LINE__);
    }
    for (const auto &community: communities) {
        // 检测k-团
        assert(community.id2node.find(query_node) != community.id2node.end());
        vector<long long> neigh_nodes;
        vector<pair<Graphs, vector<pair<long long, long long>>>> deltaBlocks;
        unordered_map<long long, pair<Graphs, vector<pair<long long, long long>>>> n2g;
        for (const auto &neighbor: community.id2node.at(query_node)->connTo) {
            neigh_nodes.push_back(neighbor->node_a == query_node ? neighbor->node_b : neighbor->node_a);
        }
        if (debug_info) printf("[%d] EnumNodes.\n", __LINE__);
        vector<vector<long long>> k_clique_nodes = enumNodes(neigh_nodes, k - 1);
        if (debug_info) printf("[%d] EnumNodes End.\n", __LINE__);
        neigh_nodes.clear();    // 清空
        for (auto &knodes : k_clique_nodes) {
            Graphs cand_B;
            knodes.emplace_back(query_node);   // 增加查询节点
            cand_B.newGraphsFrom(knodes, community);
            if (checkKClique(cand_B)) {
                if (debug_info) printf("[%d] Enum Period.\n", __LINE__);
                auto infos = enmuTopkTCCPeriodEqual(cand_B); // min, max
                if (debug_info) printf("[%d] Enum Period End.\n", __LINE__);
                assert(SIZE(infos) > 0);
                long long interval = infos.at(0).second - infos.at(0).first;
                vector<long long> conflict_nodes;
                for (const auto &node: cand_B.nodes) {
                    if (n2g.find(node->node_id) != n2g.end()) {
                        conflict_nodes.emplace_back(node->node_id);
                    }
                }
                if (conflict_nodes.empty()) {
                    for (const auto &node: cand_B.nodes) {
                        if (node->node_id == query_node) continue;
                        n2g[node->node_id] = make_pair(cand_B, infos);
                    }
                } else {
                    bool largeFlag = false;
                    bool smallFlag = false;
                    vector<long long> smallNodes;
                    for (const auto &cn: conflict_nodes) {
                        if (n2g.find(cn) != n2g.end()) {
                            auto cp = n2g.at(cn);
                            Graphs cg = cp.first;
                            auto c_info = cp.second.at(0);
                            if (c_info.second - c_info.first <= interval) {
                                largeFlag = true;   // 当前图比存储图聚集长度大
                            } else {
                                smallFlag = true;
                                smallNodes.emplace_back(cn);    // 当前图比存储图聚集长度小
                            }
                        }
                    }
                    if (largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                    } else if (!largeFlag && smallFlag) {
                        for (const auto &sn: smallNodes) {
                            if (n2g.find(sn) == n2g.end()) continue;
                            const Graphs sg = n2g.at(sn).first;
                            for (const auto &_n: sg.nodes) {
                                if (_n->node_id == query_node) continue;
                                n2g.erase(_n->node_id);
                            }
                        }
                        for (const auto &_n: cand_B.nodes) {
                            if (_n->node_id == query_node) continue;
                            assert(n2g.find(_n->node_id) == n2g.end());
                            n2g[_n->node_id] = make_pair(cand_B, infos);
                        }
                    }
                }
                if (debug_info) printf("[%d]: %d\n", __LINE__, SIZE(n2g));
            } // end k-clique check
        }   // end knode enum
        unordered_map<Graphs, vector<pair<long long, long long>>, GraphsHash, GraphsComp> _tmpstore;
        for (const auto &_e: n2g) _tmpstore[_e.second.first] = _e.second.second;

        deltaBlocks.assign(begin(_tmpstore), end(_tmpstore));
        for (auto &c_p: deltaBlocks) {
            Graphs cand_B = c_p.first;
            vector<pair<long long, long long>> infos = c_p.second;
            Truss minimalTruss;
            map<long long, vector<Graphs>> innerP2gs; // period to graphs
            truss_decomposition(cand_B, minimalTruss);
            if (debug_on) {
                printf("[%d]: basic block nodes:", __LINE__);
                for (const auto &node: cand_B.nodes) {
                    printf("%lld", node->node_id);
                }
                printf("\n[%d]basic block edges:", __LINE__);
                for (const auto &edge: cand_B.edges) {
                    printf("(%lld, %lld):", edge->node_a, edge->node_b);
                    for (const auto &oc:edge->occur) printf("%lld, ", oc);
                }
                printf("\n");
            }

            block2community.insert(make_pair(cand_B, community));
            block2truss.insert(make_pair(cand_B, minimalTruss));
            block2spans[cand_B].resize(topk);
            block2info[cand_B].resize(topk);
            for (const auto &each_info: infos) {
                auto topkPair = enmuTopkTCCPeriodNotOptiz(cand_B, each_info, topk);
                vector<vector<pair<long long, vector<long long>>>> spans = topkPair.first;
                vector<pair<long long, long long>> topkinfos = topkPair.second;
                assert(!spans.empty());
                assert(SIZE(spans) <= topk);
                assert(SIZE(topkinfos) <= topk);
                for (long long _topi = 0; _topi < SIZE(spans); _topi++) {
                    block2spans[cand_B][_topi].emplace_back(spans.at(_topi));
                }
                for (long long _topi = 0; _topi < SIZE(topkinfos); _topi++) {
                    block2info[cand_B][_topi].emplace_back(topkinfos.at(_topi));
                }
                // 将当前delta基本块 topk放入
                for (const auto &info: topkinfos) {
                    if (innerP2gs.find(info.second - info.first) == innerP2gs.end()) {
                        innerP2gs[info.second - info.first].emplace_back(cand_B);
                    } else {
                        auto interval = info.second - info.first;
                        if (std::find(innerP2gs[interval].begin(), innerP2gs[interval].end(), cand_B) ==
                            innerP2gs[interval].end()) {
                            innerP2gs[interval].emplace_back(cand_B);
                        }
                    }
                }
                auto _pit = p2gs.begin();
                auto _ipit = innerP2gs.begin();
                while (_pit != p2gs.end() && _ipit != innerP2gs.end()) {
                    if (_pit->first < _ipit->first) _pit++;
                    else if (_pit->first == _ipit->first) {
                        for (const auto &_g: _ipit->second) {
                            if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                                _pit->second.emplace_back(_g);
                            }
                        }
                        _pit++, _ipit++;
                    } else {
                        if (SIZE(p2gs) == topk) {
                            auto _iter = p2gs.begin();
                            std::advance(_iter, SIZE(p2gs) - 1);
                            _pit = p2gs.erase(_iter);
                        }
                        for (const auto &_g: _ipit->second) {
//                            if (std::find(_ipit->second.begin(), _ipit->second.end(), _g) == _ipit->second.end()) {
                            if (std::find(p2gs[_ipit->first].begin(), p2gs[_ipit->first].end(), _g) ==
                                p2gs[_ipit->first].end()) {
                                p2gs[_ipit->first].emplace_back(_g);
                            }
                        }
                        _ipit++;
                    }
                }
                if (SIZE(p2gs) < topk) {
                    while (_ipit != innerP2gs.end()) {
                        for (const auto &_g: _ipit->second) {
//                            if (std::find(_pit->second.begin(), _pit->second.end(), _g) == _pit->second.end()) {
                            if (std::find(p2gs[_ipit->first].begin(), p2gs[_ipit->first].end(), _g) ==
                                p2gs[_ipit->first].end()) {
                                p2gs[_ipit->first].emplace_back(_g);
                            }
                        }
                        _ipit++;
                    }
                }
            } // end each info
        } // end-for loop delta-blocks
    }   // end community
    if (debug_info) printf("[%d]:finishing k-clique detection\n", __LINE__);

    assert(p2gs.size() <= topk);
    assert(!p2gs.empty());
    // 记录blocks
    deque<BInfo *> BQ; // init
    unordered_map<Graphs, long long, GraphsHash, GraphsComp> g2rank;
    vector<pair<Span, Info>> ans;
    unordered_set<vector<pair<long long, vector<long long>>>, VecPairHash<long long>, VecPairComp<long long>> tgRec;
    for (const auto &gs: p2gs)
        for (const auto &g : gs.second)
            g2rank[g] = 0;
    for (auto iter = p2gs.begin(); iter != p2gs.end(); iter++) {
        vector<Graphs> gs = iter->second;
        for (int _bi = 0; _bi < SIZE(gs); ++_bi) {
            Graphs B = gs.at(_bi);
            assert(block2community.find(B) != block2community.end());
            Graphs &community = block2community.at(B);
            assert(block2truss.find(B) != block2truss.end());
            Truss Btruss = block2truss.at(B);
            assert(block2spans.find(B) != block2spans.end());
            assert(block2info.find(B) != block2info.end());
            assert(g2rank.find(B) != g2rank.end());
            if (g2rank[B] >= topk) continue;
            vector<vector<pair<long long, vector<long long>>>> t_spans = block2spans.at(B)[g2rank[B]];
            vector<pair<long long, long long>> t_infos = block2info.at(B)[g2rank[B]];
            g2rank[B]++;
            assert(SIZE(t_infos) == SIZE(t_infos));
            for (long long _ti = 0; _ti < SIZE(t_infos); _ti++) {
                auto binfo = new BInfo(community, B.deepCopy(), Btruss, t_spans.at(_ti), t_infos.at(_ti), false);
                BQ.emplace_back(binfo);
            }
        }
    }

    // 按聚集社区长度重新排序
    std::sort(BQ.begin(), BQ.end(), [](const BInfo *a, const BInfo *b) -> bool {
        return a->info.second - a->info.first < b->info.second - b->info.first;
    });
    timer->end("Starting calculating (Before BQ)");
    int k_rec[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 20, 25, 30, 50, 100};
    unordered_set<int> ku_rec(begin(k_rec), end(k_rec));
    timer->start();
    long long prev_val = INT32_MIN;
    long long cur_topk = 0;
    while (!BQ.empty()) {
        BInfo *binfo = BQ.front();
        BQ.pop_front();

        // 最小聚集社区
        if (binfo->status) {
            if (prev_val < binfo->info.second - binfo->info.first) {
                prev_val = binfo->info.second - binfo->info.first;
                cur_topk++; // 更新当前topk值
            }
            if (cur_topk > topk) break;
            if (ku_rec.find(cur_topk) != ku_rec.end()) {
                timer->end("end with top-" + to_string(cur_topk));
                timer->start();
            }
            ans.emplace_back(make_pair(binfo->span, binfo->info));
            continue;
        } else { // 未构成最大聚集社区
            // 获取最新状态
            Graphs community = binfo->community;
            Graphs B = binfo->g;
            long long curNodeSize = SIZE(B.nodes);
            bool judgement = false;
            Truss Btruss = binfo->truss;
            Span span = binfo->span;
            Info info = binfo->info;

            unordered_set<long long> vistedNodes;
            deque<long long> Q;
            for (const auto &v: B.nodes) {
                vistedNodes.insert(v->node_id);
                Q.push_back(v->node_id);
            }
            // graph expansion
            while (SIZE(vistedNodes) < SIZE(community.nodes)) {
                long long _curNode = Q.front();
                Q.pop_front();

                for (const auto &outer: community.id2node.at(_curNode)->connTo) {
                    long long outerNodes = outer->node_a == _curNode ? outer->node_b : outer->node_a;
                    if (vistedNodes.find(outerNodes) == vistedNodes.end()) {
                        vistedNodes.insert(outerNodes);
                        assert(community.hashedEdge.find(to_encode_edge(outerNodes, _curNode)) !=
                               community.hashedEdge.end());
                        Edge *outerEdge = community.hashedEdge.at(to_encode_edge(outerNodes, _curNode));
                        updateTruss(B, outerEdge, Btruss);
                        for (const auto &node: neighbors(community, to_encode_edge(outerNodes, _curNode))) {
                            if (B.id2node.find(node) != B.id2node.end() &&
                                B.hashedEdge.find(to_encode_edge(node, outerNodes)) ==
                                B.hashedEdge.end()) {
                                assert(community.hashedEdge.find(to_encode_edge(node, outerNodes)) !=
                                       community.hashedEdge.end());
                                updateTruss(B, community.hashedEdge.at(to_encode_edge(node, outerNodes)),
                                            Btruss);
                            }
                        }
                        Q.push_back(outerNodes);
                        // detect k-truss maintain
                        bool bFound = true;
                        for (const auto &_perTruss: Btruss) {
                            if (debug_on) {
                                auto _p = to_decode_edge(_perTruss.first); // debug
                                printf("[%d]: (%lld, %lld): truss: %lld\n", __LINE__, _p.first, _p.second,
                                       _perTruss.second); //debug
                            }
                            if (_perTruss.second < k) {
                                bFound = false;
                                break;
                            }
                        }
                        if (bFound) {
                            auto update_p = updateTopkTCCPeriodNoOptiz(B, span, info, topk);
                            vector<Span> vspan = update_p.first;
                            vector<Info> vinfo = update_p.second;

                            assert(SIZE(vspan) == SIZE(vinfo));
                            for (long long _i = 0; _i < SIZE(vinfo); _i++) {
                                Span u_span = vspan.at(_i);
                                Info u_info = vinfo.at(_i);
                                if (_i == 0) {
                                    if (!(u_info.first == info.first && u_info.second == info.second)) {
                                        if (tgRec.find(span) == tgRec.end()) {
                                            tgRec.insert(span);
                                            Graphs _;
                                            Truss __;
                                            auto oribinfo = new BInfo(_, _, __, span, info, true);
                                            BQ.emplace_back(oribinfo);
                                            auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                      false);
                                            BQ.emplace_back(newbinfo);
                                            judgement = true;

                                            goto L1;
                                        }
                                    } else {
                                        auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info,
                                                                  false);
                                        BQ.emplace_back(newbinfo);

                                        goto L1;
                                    }
                                } else {
                                    auto newbinfo = new BInfo(community, B.deepCopy(), Btruss, u_span, u_info, false);
                                    BQ.emplace_back(newbinfo);

                                    goto L1;
                                }
                            }
                        }   // end if bFound
                    }
                }   // end for neighbor nodes
            } //End 子图扩展
            // 最大扩展至社区规模
            L1:
            if (!judgement && SIZE(vistedNodes) == SIZE(community.nodes)) {
                Graphs _;
                Truss __;
                auto oribinfo = new BInfo(_, _, __, span, info, true);
                BQ.emplace_back(oribinfo);
            }
        }

        // 按聚集社区长度重新排序
        std::sort(BQ.begin(), BQ.end(), [](const BInfo *a, const BInfo *b) -> bool {
            return a->info.second - a->info.first < b->info.second - b->info.first;
        });
    }
    timer->end("FASTTCCS COST");
    ct_density(ans[0].second, ans[0].first);
    return ans;
}

long long detect_shortest_length(const Graphs &g) {
    assert(g.edges.size() > 1);
    Edge *edge = g.edges.at(0);
    pair<long long, long long> minimalPair;
    vector<long long> init_intervals;
    for (const auto &oc: edge->occur) init_intervals.emplace_back(oc);

    for (int _i = 1; _i < SIZE(g.edges); ++_i) {
        Edge *cur_edge = g.edges.at(_i);
        vector<long long> vals;
        if (_i == 1) {
            unordered_map<long long, pair<long long, long long>> id2edges;
            for (long long _ei = 0; _ei < SIZE(init_intervals); ++_ei) {
                for (long long _ej = 0; _ej < SIZE(cur_edge->occur); ++_ej) {
                    auto minVal = std::min(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    auto maxVal = std::max(init_intervals.at(_ei), cur_edge->occur.at(_ej));
                    vals.emplace_back(abs(init_intervals.at(_ei) - cur_edge->occur.at(_ej)));
                    id2edges.insert(make_pair(_ej + _ei * SIZE(cur_edge->occur),
                                              make_pair(minVal, maxVal)));
                }
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            minimalPair = id2edges.at(idx.at(0)); // 0: min, 1: max
        } else {
            unordered_map<long long, long long> id2edges;
            for (long long _ej = 0; _ej < SIZE(cur_edge->occur); _ej++) {
                auto oc = cur_edge->occur.at(_ej);
                if (oc <= minimalPair.second && oc >= minimalPair.first) {
                    vals.emplace_back(abs(minimalPair.second - minimalPair.first));
                } else {
                    vals.emplace_back(std::max(abs(oc - minimalPair.first), abs(oc - minimalPair.second)));
                }
                id2edges.insert(make_pair(_ej, oc));
            }
            vector<size_t> idx = sort_indexes(vals);
            assert(SIZE(idx) > 0);
            long long curVal = id2edges.at(idx.at(0));
            minimalPair.first = std::min(minimalPair.first, curVal);
            minimalPair.second = std::max(minimalPair.second, curVal);
        } // end else
    }

//    printf("minium Size: %d.\n", minimalPair.second - minimalPair.first);
    return minimalPair.second - minimalPair.first;
}

void ct_density(const Graphs &g) {
    auto node_size = SIZE(g.nodes);
    auto clustering_length = detect_shortest_length(g);
    auto sum_outer = 0.0f;
    long long edge_num = 0;
    for (auto _dxi = 0; _dxi < SIZE(g.edges); _dxi++) {
        for (auto _dxj = _dxi + 1; _dxj < SIZE(g.edges); _dxj++) {
            for (const auto& oci: g.edges.at(_dxi)->occur) {
                for (const auto& ocj: g.edges.at(_dxj)->occur) {
                    auto delta = abs(oci - ocj);
                    sum_outer += delta;
                    edge_num++;
                }
            }
        }
    }

    auto sum_expected = clustering_length;
    sum_outer = sum_outer / edge_num;
    printf("Calculating .......\n |%f-%lld|/%lld=%f\n", sum_outer, sum_expected, clustering_length,
           abs(sum_outer - sum_expected) / (clustering_length));
}

void ct_density(const Info &info, const Span &span) {
    auto clustering_length = info.second - info.first;
    unordered_set<long long> nodes;
    auto sum_outer = 0.0f;
    long long edge_num = 0;
    for (const auto& s: span) {
        auto p = to_decode_edge(s.first);
        nodes.insert(p.first);
        nodes.insert(p.second);
    }

    for (auto _dxi = 0; _dxi < SIZE(span); _dxi++) {
        for (auto _dxj = _dxi + 1; _dxj < SIZE(span); _dxj++) {
            for (const auto& oci : span.at(_dxi).second) {
                for (const auto& ocj : span.at(_dxj).second) {
                    long long delta = abs(oci - ocj);
                    sum_outer += delta;
                    edge_num ++;
                }
            }

        }
    }
    auto node_size = SIZE(nodes);
    auto sum_expected = clustering_length;
    sum_outer = sum_outer / edge_num;
    printf("Calculating .......\n |%f-%lld|/%lld=%f\n", sum_outer, sum_expected, clustering_length,
           abs(sum_outer - sum_expected) / (clustering_length));
}