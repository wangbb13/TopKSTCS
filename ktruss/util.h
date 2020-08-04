//
// Created by Luo on 2020/3/3.
//

#ifndef SOURCE_UTIL_H
#define SOURCE_UTIL_H

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <sstream>
#include <list>
#include <set>
#include <queue>
#include <deque>
#include <algorithm>
#include <random>
#include <functional>
#include <cmath>
#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <stack>
#include <unistd.h>
#include "timer.h"
#include <cstdlib>
#include <stdio.h>
#include <cassert>
#include "json.hpp"
#include <iterator>

using json = nlohmann::json;
using namespace std;

typedef unordered_set<long long> Nodes;
typedef unordered_map<long long, unordered_set<long long>> Graph;
typedef vector<Graph> Communities;
typedef unordered_map<long long, unordered_map<long long, long long>> Branch;
typedef unordered_set<long long> HashedEdge;
typedef unordered_map<long long, Graph> TemporalGraph;
typedef unordered_map<long long, long long> Truss;
typedef vector<pair<long long, vector<long long>>> Span;
typedef pair<long long, long long> Info;
struct Node;
struct Edge;

#define SIZE(x) int(x.size())

struct Config {
    long long query_node;
    long long topk;
    long long delta_truss;
};

namespace ns {
    void from_json(const json &j, Config &c);
}

/*
* Cantor pairing function
*/
long long to_encode_edge(long long a, long long b, bool is_undirected = true);

/*
*  Inverting Cantor pairing function
*/
pair<long long, long long> to_decode_edge(long long val, bool is_undirected = true);

struct SuperNode {
    long long super_id;
    long long truss;
    unordered_map<long long, unordered_set<long long>> edges;

    SuperNode(long long _sn) : super_id(_sn), truss(-1) {
    }
};

struct Node {
    long long node_id;
    vector<Edge *> connTo;

    Node() : node_id(-1) {
    };

    Node(long long nodeid) : node_id(nodeid) {
        this->node_id = nodeid;
    }
};

struct Edge {
    bool bDirected;
    long long node_a;
    long long node_b;
    vector<long long> occur;

    Edge() : node_a(-1), node_b(-1), bDirected(false) {
    };

    Edge(long long nodeid1, long long nodeid2) : node_a(nodeid1), node_b(nodeid2), bDirected(false) {
    }

    Edge(long long nodeid1, long long nodeid2, long long temporal) : node_a(nodeid1), node_b(nodeid2),
                                                                     bDirected(false) {
        occur.emplace_back(temporal);
    }

    Edge(long long nodeid1, long long nodeid2, long long temporal, bool is_directed) : node_a(nodeid1), node_b(nodeid2),
                                                                                       bDirected(is_directed) {
        occur.emplace_back(temporal);
    }
};

/*
* Cantor pairing function
*/
long long to_encode_edge(const Edge *edge, bool is_undirected = true);

struct Graphs {
    vector<Node *> nodes;
    vector<Edge *> edges;

    unordered_map<long long, Edge *> hashedEdge;
    unordered_map<long long, Node *> id2node;

    Node *newNode(long long nodeid) {
        Node *node = nullptr;
        if (id2node.find(nodeid) != id2node.end()) {
            node = id2node[nodeid];
        } else {
            node = new Node(nodeid);
            id2node.insert(make_pair(nodeid, node));

            nodes.emplace_back(node);
        }

        return node;
    }

    Edge *newEdge(long long from, long long to, long long temporal, bool is_directed = false) {
        Edge *edge = nullptr;
        long long hashCode = to_encode_edge(from, to);
        if (hashedEdge.find(hashCode) != hashedEdge.end()) {
            edge = hashedEdge[hashCode];
            hashedEdge[hashCode]->occur.emplace_back(temporal);
        } else {
            edge = new Edge(from, to, temporal, is_directed);
            hashedEdge.insert(make_pair(hashCode, edge));

            assert(id2node.find(from) != id2node.end());
            assert(id2node.find(to) != id2node.end());

            id2node[from]->connTo.emplace_back(edge);
            id2node[to]->connTo.emplace_back(edge);

            edges.emplace_back(edge);
        }

        return edge;
    }

    Edge *newEdgeFrom(Edge *edge) {
        assert(hashedEdge.find(to_encode_edge(edge->node_a, edge->node_b)) == hashedEdge.end());
        if (id2node.find(edge->node_b) == id2node.end() && id2node.find(edge->node_a) == id2node.end()) {
            Node *nodeB = new Node(edge->node_b);
            nodeB->connTo.emplace_back(edge);
            Node *nodeA = new Node(edge->node_a);
            nodeA->connTo.emplace_back(edge);

            nodes.emplace_back(nodeA);
            nodes.emplace_back(nodeB);
            id2node[edge->node_b] = nodeB;
            id2node[edge->node_a] = nodeA;
        } else if (id2node.find(edge->node_b) == id2node.end()) {
            Node *node = new Node(edge->node_b);
            node->connTo.emplace_back(edge);
            id2node.at(edge->node_a)->connTo.emplace_back(edge);

            nodes.emplace_back(node);
            id2node[edge->node_b] = node;
        } else if (id2node.find(edge->node_a) == id2node.end()) {
            Node *node = new Node(edge->node_a);
            node->connTo.emplace_back(edge);
            id2node.at(edge->node_b)->connTo.emplace_back(edge);

            nodes.emplace_back(node);
            id2node[edge->node_a] = node;
        } else {
            id2node.at(edge->node_b)->connTo.emplace_back(edge);
            id2node.at(edge->node_a)->connTo.emplace_back(edge);
        }

        edges.emplace_back(edge);
        hashedEdge.insert(make_pair(to_encode_edge(edge->node_b, edge->node_a), edge));
    }

    void newGraphsFrom(vector<long long> cand_nodes, const Graphs &g) {
        for (int i = 0; i < SIZE(cand_nodes); i++) {
            long long node_id = cand_nodes.at(i);
            if (this->id2node.find(node_id) == this->id2node.end()) {
                Node *node = new Node(node_id);
                this->id2node.insert(make_pair(node_id, node));
                this->nodes.emplace_back(node);
            }
            for (int j = i + 1; j < SIZE(cand_nodes); j++) {
                long long ano_node_id = cand_nodes.at(j);
                if (this->id2node.find(ano_node_id) == this->id2node.end()) {
                    Node *ano_node = new Node(ano_node_id);
                    this->id2node.insert(make_pair(ano_node_id, ano_node));
                    this->nodes.emplace_back(ano_node);
                }
                for (const auto &edge: g.id2node.at(node_id)->connTo) {
                    long long n = edge->node_a == node_id ? edge->node_b : edge->node_a;
                    if (n == ano_node_id) {
                        this->id2node.at(node_id)->connTo.emplace_back(edge);
                        this->id2node.at(ano_node_id)->connTo.emplace_back(edge);
                        this->hashedEdge.insert(make_pair(to_encode_edge(ano_node_id, node_id), edge));
                        this->edges.emplace_back(edge);
                    }
                }
            }
        }
    }

    Graphs deepCopy() const {
        Graphs dg;
        for (const auto &node: this->nodes) {
            auto ptrNode = new Node(node->node_id);
            for (const auto &edge: node->connTo) {
                ptrNode->connTo.emplace_back(edge);
            }
            dg.nodes.emplace_back(ptrNode);
            dg.id2node[node->node_id] = ptrNode;
        }

        for (const auto &edge: this->edges) {
            dg.edges.emplace_back(edge);
            dg.hashedEdge.insert(make_pair(to_encode_edge(edge->node_a, edge->node_b), edge));
        }

        return dg;
    }

    bool operator==(const Graphs &rhs) {
        return this->nodes.size() == rhs.nodes.size() && this->edges.size() == rhs.edges.size() &&
               *(this->nodes.begin()) == *(this->nodes.begin()) && *(this->edges.begin()) == *(rhs.edges.begin());
    }
};

struct BInfo {
    Graphs g;
    Truss truss;
    Span span;
    Info info;
    bool status;
    Graphs community;

    BInfo(Graphs& community, Graphs g, Truss truss, Span span, Info info, bool status = false) {
        this->community = community;
        this->g = g;
        this->truss = truss;
        this->span = span;
        this->info = info;
        this->status = status;
    }
};

template<typename T>
struct PairHash {
    size_t operator()(const pair<T, T> &rhs) const {
        return hash<T>()(to_encode_edge(rhs.first, rhs.second));
    }
};

template<typename T>
struct VecPairHash {
    size_t operator()(const vector<pair<T, vector<T>>> &rhs) const {
        long long _t = 0;
        for (const auto &e: rhs) {
            _t += e.first;
        }

        return hash<T>()(_t);
    }
};

template<typename T>
struct VecPairComp {
    bool operator()(const vector<pair<T, vector<T>>> &_lhs, vector<pair<T, vector<T>>> &_rhs) const {
        auto lhs = _lhs;
        auto rhs = _rhs;
        if (SIZE(lhs) != SIZE(rhs)) {
            return false;
        }
        std::sort(begin(lhs), end(lhs), [](const pair<T, vector<T>> &a, const pair<T, vector<T>> &b) -> bool {
            return a.first < b.first;
        });
        std::sort(begin(rhs), end(rhs), [](const pair<T, vector<T>> &a, const pair<T, vector<T>> &b) -> bool {
            return a.first < b.first;
        });

        for (long long _i = 0; _i < SIZE(lhs); _i++) {
            auto _la = lhs.at(_i);
            auto _ra = rhs.at(_i);
            if (_la.first != _ra.first || SIZE(_la.second) != SIZE(_ra.second)) {
                return false;
            }

            for (long long _j = 0; _j < SIZE(_la.second); _j++) {
                auto _loc = _la.second.at(_j);
                auto _roc = _ra.second.at(_j);
                if (_loc != _roc) {
                    return false;
                }
            }
        }

        return true;
    }
};

template<typename T>
struct PairComp {
    bool operator()(const pair<T, T> &lhs, const pair<T, T> &rhs) const {
        return lhs.first == rhs.first && lhs.second == rhs.second;
    }
};

struct GraphsHash {
    size_t operator()(const Graphs &rhs) const {
        return hash<long long>()(rhs.nodes.size()) ^ hash<long long>()(rhs.edges.size());
    }
};

struct GraphsComp {
    bool operator()(const Graphs &lhs, const Graphs &rhs) const {
        return lhs.nodes.size() == rhs.nodes.size() && lhs.edges.size() == rhs.edges.size() &&
               *(lhs.nodes.begin()) == *(rhs.nodes.begin()) && *(lhs.edges.begin()) == *(rhs.edges.begin()) &&
               *(lhs.nodes.begin() + SIZE(lhs.nodes) - 1) == *(rhs.nodes.begin() + SIZE(rhs.nodes) - 1) &&
               *(lhs.edges.begin() + SIZE(lhs.edges) - 1) == *(rhs.edges.begin() + SIZE(rhs.edges) - 1);
    }
};

struct TemporalGraphsComp {
    bool operator()(const Graphs &lhs, const Graphs &rhs) const {
        long long _lts = 0;
        long long _rts = 0;
        for (const auto &edge: lhs.edges)
            for (const auto &oc: edge->occur)
                _lts += oc;
        for (const auto &edge: rhs.edges)
            for (const auto &oc: edge->occur)
                _rts += oc;
        return lhs.nodes.size() == rhs.nodes.size() && lhs.edges.size() == rhs.edges.size() &&
               *(lhs.nodes.begin()) == *(rhs.nodes.begin()) && *(lhs.edges.begin()) == *(rhs.edges.begin()) &&
               *(lhs.nodes.begin() + SIZE(lhs.nodes) - 1) == *(rhs.nodes.begin() + SIZE(rhs.nodes) - 1) &&
               *(lhs.edges.begin() + SIZE(lhs.edges) - 1) == *(rhs.edges.begin() + SIZE(rhs.edges) - 1) &&
               _lts == _rts;
    }
};

struct ConsistentGraph {
    long long consistent_id;

    unordered_map<long long, Graphs> cid2g;
    unordered_map<long long, vector<vector<pair<long long, long long>>>> cid2s;

    ConsistentGraph() {

    }

    void put(Graphs _g, vector<vector<pair<long long, long long>>> _s) {
        if (cid2g.empty()) {
            this->consistent_id = 0;
        } else {
            this->consistent_id = next_id();
        }
        cid2g.insert(make_pair(this->consistent_id, _g));
        cid2s.insert(make_pair(this->consistent_id, _s));
    }


    long long next_id() {
        assert(cid2g.size() == cid2s.size());
        return cid2s.size();
    }
};

typedef unordered_map<long long, unordered_map<long long, unordered_map<long long, long long>>> TCPIndex;
typedef unordered_map<SuperNode *, unordered_set<SuperNode *>> SuperGraph;


long long union_find(long long x, unordered_map<long long, long long> &c);

long long union_find(long long x, vector<long long> &c);

void union_join(long long x, long long y, unordered_map<long long, long long> &c);

void union_join(long long x, long long y, vector<long long> &c);

void
equiTruss_community_search(const SuperGraph &superGraph, const unordered_map<long long, unordered_set<long long>> &H,
                           const Truss &truss, long long k, long long query_node, Communities *&__communities);

unordered_map<long long, unordered_set<long long>>
equiTruss_index_contruction(const Graph &projected_graph, const Truss &truss, const HashedEdge &temporal_edge_hash,
                            long long max_truss, SuperGraph &__superGraph);

Branch tcp_index_construction(const Graph &graph, Truss &graph_truss, TCPIndex &__tx);

void dfs_visit(const Graph &g, Nodes &visited, long long node);

long long truss_decomposition(Graph &graph, Truss &__truss);

long long truss_decomposition(Graphs &g, Truss &__truss);

void load_temporal_networks(const string &filename, Graphs &__graphs, long long &last_timestamp);

void load_temporal_networks(const string &filename, Nodes &g_nodes, HashedEdge &g_hashedEdge, Graph &g_graph,
                            TemporalGraph &g_temporal_graph, long long &last_timestamp);

void
processEdge(long long u, long long v, const Truss &truss, const long long k, const long long snId,
            unordered_map<long long, bool> &processed, deque<long long> &Q,
            unordered_map<long long, unordered_set<long long>> &edge_list);

void
merge_graph(Graph &g, const unordered_map<long long, unordered_set<long long>> &edges);

long long cal_temporal_edges(const TemporalGraph &g_temporal_graph);

vector<Graphs> baseline_community_detection_with_truss(Graphs g, const Truss &truss, const long long k);

vector<Graphs>
baseline_community_search_with_truss(Graphs g, const Truss &truss, const long long k, const long long vq);

void __enumNodes(const vector<long long> &nodes, const long long k, vector<long long> &ans, long long counter,
                 vector<vector<long long>> &__vec);

vector<vector<long long>> enumNodes(const vector<long long> &nodes, const long long k);

vector<vector<pair<long long, long long>>> enmuPeriod(const Graphs &g, const long long topk);

vector<vector<pair<long long, long long>>>
updatePeriod(const Graphs &g, const Graphs &newG, const vector<vector<pair<long long, long long>>> &spans);

vector<vector<pair<long long, long long>>>
updatePeriod(const Graphs &g, const vector<vector<pair<long long, long long>>> &spans);

vector<vector<pair<long long, long long>>> enmuMTCCPeriod(const Graphs &g, const long long topk);
pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
enmuTopkTCCPeriodNotOptiz(const Graphs &g, const pair<long long, long long> &info, const long long topk);
pair<long long, long long> enmuTopkTCCPeriodByOne(const Graphs &g);

vector<pair<long long, long long>> enmuTopkTCCPeriodEqual(const Graphs &g);

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
enmuTopkTCCPeriod(const Graphs &g, const pair<long long, long long> &info, const long long topk);

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
updateTopkTCCPeriod(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                    const pair<long long, long long> &info, const long long topk);

pair<vector<vector<pair<long long, vector<long long>>>>, vector<pair<long long, long long>>>
updateTopkTCCPeriodNoOptiz(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                    const pair<long long, long long> &info, const long long topk);

pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>
updateTopkTCCPeriodByOne(const Graphs &g, const vector<pair<long long, vector<long long>>> &span,
                         const pair<long long, long long> &info);

vector<vector<pair<long long, long long>>>
updateMTCCPeriod(const Graphs &g, const vector<pair<long long, long long>> &span);

vector<vector<pair<long long, long long>>>
updateMTCCPeriodNotEmpty(const Graphs &g, const vector<pair<long long, long long>> &span, const long long &topk);

vector<vector<pair<long long, long long>>>
expandMTCCPeriodNotEmpty(const Graphs &g, const vector<pair<long long, long long>> &span, const long long &topk);


template<typename T>
vector<size_t> sort_indexes(const vector<T> &v);

/*
 * graph: it will be added a new edge
 * edgeCode: inserted edge
 * __truss: updated Truss
 */
void updateTruss(Graphs &g, Edge *edge, Truss &__truss);

pair<long long, long long> calculateK1K2(const Graphs &g, const Edge *edge, const Truss &truss, const long long maxK);

vector<long long> neighbors(const Graphs &g, long long edgeCode);

bool graphEq(const Graphs &g1, const Graphs &g2);

vector<vector<pair<long long, long long>>> MTCC(Graphs &g, long long _k, long long _topk, long long _query_node);

vector<vector<pair<long long, long long>>> TopKTCC(Graphs &g, long long _k, long long _topk, long long _query_node);

vector<vector<pair<long long, long long>>>
MTCC_Fast(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast = false);

vector<vector<pair<long long, long long>>>
TopKTCC_Fast(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast = false);

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCC(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast = false);

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCCS(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast = false);

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
FastTopKTCCS_L(Graphs &g, long long _k, long long _topk, long long _query_node, FILE *fp, bool reduction_fast = false);

vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>>
BackUp(Graphs &g, long long _k, long long _topk, long long _query_node, bool reduction_fast = false);

long long find_idx_by_range(const long long &idx, const vector<long long> &vec);

void log_results(vector<vector<pair<long long, long long>>> &log, FILE *fp);

void log_results(vector<pair<vector<pair<long long, vector<long long>>>, pair<long long, long long>>> &res, FILE *fp);

void enumUpdation(const long long c, const vector<vector<pair<long long, long long>>> &vals,
                  vector<pair<long long, long long>> &pos, vector<vector<pair<long long, long long>>> &_s);

pair<long long, long long> calculateRank(const Graphs &g);

bool inInterval(const vector<pair<long long, long long>> &c, const long long val);

pair<long long, vector<long long>> reCalculateRank(const Graphs &g, const long long topk);

void updateGraphByUpperBound(Graphs &g, const long long upper, const long long query_node, FILE *fp = nullptr);

void graphExpansion(Graphs &B, Truss &Btruss, const Graphs &community, const long long k, const long long topk,
                    bool reduction = false);

long long findTopkVal(const vector<vector<pair<long long, long long>>> &, const long long topk);

long long findTopkVal(const vector<pair<long long, long long>> &spans, const long long topk);

bool checkKClique(const Graphs &g);

long long detect_shortest_length(const Graphs& g);

void ct_density(const Graphs& g);

void ct_density(const Info& info, const Span& span);
#endif //SOURCE_UTIL_H