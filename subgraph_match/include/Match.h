#pragma once

#include "Graph.h"
#include "TurboGraph.h"
#include "TurboMatch.h"
#include "vf2_state_sub.h"
#include "vf3_state.h"
#include "vf3_state_super.h"
#include "vf3_state_self.h"
#include "probability_strategy.h"
#include "nodesorter.h"
#include <algorithm>
#include <fstream>
#include <ctime>

typedef bool(*match_visitor)(int n, int c1[], int c2[], void* tree_s, void *usr_data);

class VF3State;

class Match {
public:
	Match(string datafile, string communityfile, string patternfile);
	Graph* data;
	TempGraph* pattern;
	unordered_map<int, TempGraph*> communityGraphs;
	vector<TempGraph*> communityGraphsVec;
	map<vector<int>, set<vector<int>>> completeMatchPatternNodes;
	set<vector<int>> displace;
	vector<vector<int>> schemes;
	map<set<int>, set<set<int>>> completeSet;
	vector<int> equalBool;
	unordered_map<int, vector<int>> equalInData;
	unordered_map<int, vector<unordered_set<int>>> equalDiff;
	unordered_map<int, int> equalTeam;

	set<set<int>> orderTree;
	set<int> orderTree1D;
	set<set<int>> localMinTree;
	//map<set<int>, set<pair<int, int>>> IETree;
	vector<vector<int>> IETreeL;
	vector<vector<int>> IETreeS;
	vector<vector<vector<bool>>> share2NeighbourPairs;
	vector<vector<bool>> share1NeighbourPairs;

	unordered_map<int, unordered_set<int>> equals;
	unordered_map<int, int> patternEqualClass;
	map<vector<int>, set<vector<int>>> symmetryNodes;
	map<vector<int>, set<vector<int>>> completeMatchRecord;
	unordered_map<string, TempGraph*> stringMatchModel;
	map<vector<int>, vector<unordered_set<int>>> submapNodeOutEdge;
	map<vector<int>, vector<unordered_set<int>>> submapNodeInEdge;
	//有哪些社区
	vector<int> commIds;
	vector<unordered_set<int>> commoe;
	vector<unordered_set<int>> commie;
	ofstream logger;

	int ansnum;
	int internum;
	int matchType;

	int usefulCS;
	int uselessCS;
	int uselessDouble;
	int uselessUntrivial;
	int uselessCut2;
	int samecounter = 0;

	void loadPatternGraph(string filename, vector<int>& nodes
		, unordered_map<int, unordered_map<string, string>>& nodeAttributes
		, unordered_map<int, unordered_map<int, unordered_map<string, string>>>& edgeAttributes
		, vector<unordered_set<int>>& outedges
		, vector<unordered_set<int>>& inedges, vector<int>* nodeLabels = NULL);

	void loadPattern(string filename);
	void initCompleteMatchNodes();
	void handleMatchPattern(unordered_map<string, vector<vector<int>>>& isomorphicList
		, map<vector<int>, string>& isomap);
	void handleExchange(unordered_map<string, vector<vector<int>>>& isomorphicList
		, map<vector<int>, string>& isomap);
	void retrivalNodes(vector<int>& current, int pos
		, unordered_map<string, vector<vector<int>>>& isomorphicList, map<vector<int>, string>& isomap, bool added
		, vector<unordered_set<int>>& tempOut, vector<unordered_set<int>>& tempIn);
	void retrivalPatterns(vector<int>& current, int pos, bool added);
	void getAllMatchNodes(vector<int>& currents, int pos, vector<int>& t, unordered_set<int>& record, bool hasSymm);
	void initOrderTree();

	int GoMatch_vf3_comm();
	int GoMatch_vf3();
	int GoMatch_Turbo_comm();
	int GoMatch_Turbo();
	bool getAllInPatternCompleteMatch(map<int, vector<int>>& supermatch, map<int, int>& supermatchmap, string& mystr, map<int, vector<int>>::iterator& sit, vector<map<int, int>>& allmaps, map<int, int>& currentMap, unordered_set<int>& usednodes);
	bool getCompleteMatch(int* supermatchmap, vector<int>& allmaps, unordered_set<string>& record);
	bool vf3_match(VF3State &s, int *pn);
	bool match_sub(VF2StateSub* s, int* pcount, string& ans, unordered_map<int, int>& mapper, int nextn1, bool iswrite = true);
};