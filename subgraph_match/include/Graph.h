#pragma once

#ifndef GRAPH_H
#define GRAPH_H

#include <iostream>
#include <map>
#include <unordered_map>
#include <fstream>
#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <algorithm>

using namespace std;

struct LabelVList
{
	int label;
	unordered_set<int> vList;
};

struct degmodel
{
	int degree;
	int node_id;
};

static bool mydegcomp(const degmodel& a, const degmodel& b)
{
	return a.degree < b.degree;
}

struct DegreePos {
	int degree;
	int pos;
};

class Graph
{
public:
	Graph() {
		inMemory = true;
		outMaxDegree = -1;
		inMaxDegree = -1;
		maxDegree = -1;
	};
	~Graph() {};

	int communityNum;
	int nodeNum;
	int labelnum;

	vector<int> node_ids;
	set<int> graphNodes;
	vector<vector<int>> communityNodes;
	// unordered_map<int, vector<int>> communityNodes;
	vector<vector<int>> nodeInfo; //0 - Community, 1 - Label
	vector<int> nodeLabels;	
	vector<vector<vector<unordered_set<int>>>> commNetworkSet; // node - community - label - neighbours
	vector<unordered_set<int>> netWorkSet;//保存所有边便于查找
	vector<vector<int>> netWorkVec;
	//unordered_map<int, unordered_map<int, unordered_set<int>>> netWorkSetComm;
	vector<unordered_set<int>> inNetWorkSet;
	vector<vector<int>> inNetWorkVec;

	vector<vector<vector<vector<DegreePos>>>> degreePosOut;
	vector<vector<vector<vector<DegreePos>>>> degreePosIn;
	vector<vector<vector<vector<int>>>> commOutBoundary;
	vector<vector<vector<vector<int>>>> commInBoundary;
	//vector<vector<unordered_map<int, unordered_map<int, int>>>> twoHopLimitation;
	
	vector<vector<vector<unordered_map<int, int>*>>> twoHopLimitation;
	//vector<vector<vector<vector<int>>>> twoHopLimitation;
	vector<vector<vector<bool>>> hasTwoHopComms;
	vector<vector<vector<vector<bool>>>> len4Limitation;
	vector<vector<vector<vector<bool>>>> triangleLimitation;
	vector<vector<vector<vector<vector<bool>>>>> len5Limitation;
	//vector<vector<vector<vector<int>>>> hasTwoHopLabels;

	vector<vector<int>> commTotalNumTag, commMaxNumTag;

	unordered_map<int, unordered_map<int, unordered_map<int, degmodel>>> commOuts, commIns;

	//unordered_map<int, unordered_set<int>> graphEqualNodes;
	//unordered_set<int> includedNodes;
	//unordered_map<int, unordered_map<int, unordered_set<int>>> needMoreSet;

	void readCommunity(const string& pathFile);
	void readNetwork(const string& pathFile);

	bool inMemory;
	int outMaxDegree;
	int inMaxDegree;
	int maxDegree;
	vector<vector<int>> labelList;
	//vector<vector<LabelVList*>> labelNetWorkVec; // include all labels, without is null

	bool hasEdge(int src, int dst)
	{
		return (netWorkSet[src].find(dst) != netWorkSet[src].end());
	}
};

class TempGraph
{
public:
	TempGraph() {};
	TempGraph(vector<int>* n, unordered_map<int, unordered_map<string, string>>* na
		, unordered_map<int, unordered_map<int, unordered_map<string, string>>>* ea
		, vector<unordered_set<int>>* oe, vector<unordered_set<int>>* ie, int labnum
		, vector<int>* nl = NULL)
	{
		nodes = n;
		nodeAttributes = na;
		edgeAttributes = ea;
		outedges = oe;
		inedges = ie;
		ifdelete = true;
		labelnum = labnum;

		nodenum = n->size();
		nodeLabels = *nl;
		invec = new vector<vector<int>>(nodenum + 1);
		outvec = new vector<vector<int>>(nodenum + 1);

		if (nl != NULL)
		{
			labelEdgesVec = new vector<vector<LabelVList*>>(nodenum + 1, vector<LabelVList*>(labelnum, NULL));
		}

		outMaxDegree = -1;
		inMaxDegree = -1;
		maxDegree = -1;

		for (int n1 = 1; n1 < inedges->size(); ++n1)
		{
			inMaxDegree = max(inMaxDegree, (int)(*inedges)[n1].size());
			for (const auto& n2 : (*inedges)[n1])
			{
				(*invec)[n1].push_back(n2);
			}
			sort((*invec)[n1].begin(), (*invec)[n1].end());
		}

		for (int n1 = 1; n1 < outedges->size(); ++n1)
		{
			int myout = (*outedges)[n1].size();
			int myin = (*inedges)[n1].size();
			outMaxDegree = max(outMaxDegree, myout);
			maxDegree = max(maxDegree, myout + myin);

			for (const auto& n2 : (*outedges)[n1])
			{
				(*outvec)[n1].push_back(n2);
				if (nl != NULL)
				{
					int label = nodeLabels[n2];
					if ((*labelEdgesVec)[n1][label] != NULL)
					{
						(*labelEdgesVec)[n1][label]->vList.insert(n2);
					}
					else
					{
						LabelVList* l = new LabelVList();
						l->label = label;
						l->vList.insert(n2);
						(*labelEdgesVec)[n1][label] = l;
						neighLabels[n1].insert(label);
					}
				}
			}
			sort((*outvec)[n1].begin(), (*outvec)[n1].end());
		}
	}
	TempGraph(vector<int> n, unordered_map<int, unordered_map<string, string>>* na
		, unordered_map<int, unordered_map<int, unordered_map<string, string>>>* ea
		, vector<unordered_set<int>>* oe, vector<unordered_set<int>>* ie, int labnum
		, vector<int>* nl = NULL)
	{
		nodes = new vector<int>(n);
		nodeAttributes = na;
		edgeAttributes = ea;
		outedges = oe;
		inedges = ie;
		ifdelete = true;
		labelnum = labnum;

		nodenum = n.size();
		nodeLabels = *nl;
		invec = new vector<vector<int>>(nodenum + 1);
		outvec = new vector<vector<int>>(nodenum + 1);

		if (nl != NULL)
		{
			labelEdgesVec = new vector<vector<LabelVList*>>(nodenum + 1, vector<LabelVList*>(labelnum, NULL));
		}

		outMaxDegree = -1;
		inMaxDegree = -1;
		maxDegree = -1;

		for (int n1 = 1; n1 < inedges->size(); ++n1)
		{
			inMaxDegree = max(inMaxDegree, (int)(*inedges)[n1].size());
			for (const auto& n2 : (*inedges)[n1])
			{
				(*invec)[n1].push_back(n2);
			}
			sort((*invec)[n1].begin(), (*invec)[n1].end());
		}

		for (int n1 = 1; n1 < outedges->size(); ++n1)
		{
			int myout = (*outedges)[n1].size();
			int myin = (*inedges)[n1].size();
			outMaxDegree = max(outMaxDegree, myout);
			maxDegree = max(maxDegree, myout + myin);

			for (const auto& n2 : (*outedges)[n1])
			{
				(*outvec)[n1].push_back(n2);
				if (nl != NULL)
				{
					int label = nodeLabels[n2];
					if ((*labelEdgesVec)[n1][label] != NULL)
					{
						(*labelEdgesVec)[n1][label]->vList.insert(n2);
					}
					else
					{
						LabelVList* l = new LabelVList();
						l->label = label;
						l->vList.insert(n2);
						(*labelEdgesVec)[n1][label] = l;
						neighLabels[n1].insert(label);
					}
				}
			}
			sort((*outvec)[n1].begin(), (*outvec)[n1].end());
		}
	}
	~TempGraph()
	{
		if (ifdelete)
		{
			(*nodes).clear();
			delete nodes;
		}
	}
	unordered_set<int>* nodeset;
	vector<int>* nodes;
	unordered_map<int, unordered_map<string, string>>* nodeAttributes;
	unordered_map<int, unordered_map<int, unordered_map<string, string>>>* edgeAttributes;
	vector<unordered_set<int>>* outedges;
	vector<unordered_set<int>>* inedges;
	vector<vector<int>>* invec;
	vector<vector<int>>* outvec;
	vector<vector<LabelVList*>>* labelEdgesVec;
	unordered_map<int, unordered_set<int>> neighLabels;
	vector<int> nodeLabels;
	vector<int> idMapping;
	
	bool ifdelete;
	int nodenum;
	int labelnum;
	int outMaxDegree;
	int inMaxDegree;
	int maxDegree;

	bool HasEdge(int src, int dst)
	{
		return ((*outedges)[src].find(dst) != (*outedges)[src].end());
	}
};

#endif