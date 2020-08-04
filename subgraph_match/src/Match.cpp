#include "Match.h"
#include "utils.h"

Match::Match(string datafile, string communityfile, string patternfile)
{
	data = new Graph();
	data->readCommunity(communityfile);
	//system("pause");
	data->readNetwork(datafile);
	//system("pause");
	loadPattern(patternfile);
	//system("pause");
	// logger.open("log.dat");

	share1NeighbourPairs = vector<vector<bool>>(data->communityNum + 1, vector<bool>(data->communityNum + 1, false));
	share2NeighbourPairs = vector<vector<vector<bool>>>(data->communityNum + 1, vector<vector<bool>>(data->communityNum + 1, vector<bool>(data->communityNum + 1, false)));

	for (int i = 1; i < data->netWorkSet.size(); ++i)
	{
		int n1 = i;
		set<int> rec;
		int comm1 = data->nodeInfo[n1][0];
		for (const auto& n2 : data->netWorkSet[n1])
		{
			int comm2 = data->nodeInfo[n2][0];
			rec.insert(comm2);
			share1NeighbourPairs[comm1][comm2] = true;
		}
		vector<int> recv = vector<int>(rec.begin(), rec.end());
		for (int p = 0; p < recv.size(); ++p)
		{
			for (int q = 0; q < recv.size(); ++q)
			{
				share2NeighbourPairs[comm1][recv[p]][recv[q]] = true;
			}
		}
	}

	ansnum = 0;
	internum = 0;
	matchType = 1;

	usefulCS = 0;
	uselessCS = 0;
	uselessDouble = 0;
	uselessUntrivial = 0;
	uselessCut2 = 0;
}

void Match::loadPatternGraph(string filename, vector<int>& nodes
	, unordered_map<int, unordered_map<string, string>>& nodeAttributes
	, unordered_map<int, unordered_map<int, unordered_map<string, string>>>& edgeAttributes
	, vector<unordered_set<int>>& outedges
	, vector<unordered_set<int>>& inedges, vector<int>* nodeLabels)
{
	fstream infile(filename);
	string buff = "";

	getline(infile, buff);
	int nodenum = atoi(buff.c_str());
	nodeLabels->resize(nodenum + 1);
	outedges.resize(nodenum + 1);
	inedges.resize(nodenum + 1);

	for (int i = 0; i < nodenum; i++)
	{
		buff.clear();

		string s = "";
		getline(infile, buff);
		buff += " ";

		bool isFirst = false;
		int node_id;
		bool isAttrName = true;
		string attriname = "";

		for (int j = 0; j < buff.size(); j++)
		{
			if (buff[j] == ' ')
			{
				if (s.empty())
				{
					continue;
				}

				if (!isFirst)
				{
					isFirst = true;
					node_id = atoi(s.c_str());
					nodes.push_back(node_id);
					(*nodeLabels)[node_id] = 0;
					s.clear();
					continue;
				}

				//nodeLabels[node_id] = atoi(s.c_str());

				/*if (isAttrName)
				{
					attriname = s;
					isAttrName = false;
				}
				else
				{
					nodeAttributes[node_id][attriname] = s;
					isAttrName = true;
				}*/

				s.clear();
			}
			else
			{
				s += buff[j];
			}
		}
	}

	buff.clear();
	getline(infile, buff);
	int edgenum = atoi(buff.c_str());

	for (int i = 0; i < edgenum; i++)
	{
		buff.clear();

		string s = "";
		getline(infile, buff);
		buff += " ";

		int j = 0;
		int src, dst;
		for (; j < buff.size(); j++)
		{
			if (buff[j] == ' ')
			{
				src = atoi(s.c_str());
				break;
			}
			else
			{
				s += buff[j];
			}
		}

		s.clear();

		for (j++; j < buff.size(); j++)
		{
			if (buff[j] == ' ')
			{
				dst = atoi(s.c_str());
				break;
			}
			else
			{
				s += buff[j];
			}
		}

		s.clear();

		bool isAttrName = true;
		string attriname = "";

		for (; j < buff.size(); j++)
		{
			if (buff[j] == ' ')
			{
				if (s.empty())
				{
					continue;
				}

				if (isAttrName)
				{
					attriname = s;
					isAttrName = false;
				}
				else
				{
					edgeAttributes[src][dst][attriname] = s;
					isAttrName = true;
				}

				s.clear();
			}
			else
			{
				s += buff[j];
			}
		}

		outedges[src].insert(dst);;// atoi(edgeAttributes[src][dst]["TYPE"].c_str());
		inedges[dst].insert(src);// atoi(edgeAttributes[src][dst]["TYPE"].c_str());
	}
}

void Match::loadPattern(string filename)
{
	vector<int> nodes;
	unordered_map<int, unordered_map<string, string>>* nodeAttributes = new unordered_map<int, unordered_map<string, string>>();
	unordered_map<int, unordered_map<int, unordered_map<string, string>>>* edgeAttributes = new unordered_map<int, unordered_map<int, unordered_map<string, string>>>();
	vector<unordered_set<int>>* outedges = new vector<unordered_set<int>>();
	vector<unordered_set<int>>* inedges = new vector<unordered_set<int>>();

	unordered_map<int, unordered_map<string, unordered_set<string>>> commna;
	unordered_map<int, unordered_map<int, unordered_map<string, unordered_set<string>>>> commea;
	vector<int>* nodeLabels = new vector<int>();

	commoe = vector<unordered_set<int>>(data->communityNum + 1);
	commie = vector<unordered_set<int>>(data->communityNum + 1);

	loadPatternGraph(filename, nodes, *nodeAttributes, *edgeAttributes, *outedges, *inedges, nodeLabels);

	for (int c = 1; c <= data->communityNum; ++c)
	{
		commIds.push_back(c);
	}
	communityGraphsVec = vector<TempGraph*>(commIds.size() + 1, NULL);

	for (int i = 0; i < commIds.size(); i++)
	{
		//unordered_map<int, unordered_set<int>> interouts, interins;

		if (data->communityNodes[commIds[i]].size() > 1)
		{
			commoe[commIds[i]].insert(commIds[i]);
		}

		vector<int> cnodes(1, -1);
		unordered_set<int> cnodeset;
		unordered_map<int, int> idToNew;
		int index = 0;
		vector<int> newnodes;
		for (const auto& n : data->communityNodes[commIds[i]])
		{
			cnodes.push_back(n);
		}
		sort(cnodes.begin(), cnodes.end());
		for (const auto& n : cnodes)
		{
			idToNew[n] = index++;
		}
		vector<unordered_set<int>>* edges = new vector<unordered_set<int>>(index);
		index = 1;
		for (const auto& n : data->communityNodes[commIds[i]])
		{
			newnodes.push_back(index++);
			//cnodes.push_back(n);
			//commna[c.first]["TYPE"].insert(to_string(storage.GetNodeType(to_string(n).c_str())));

			for (const auto& neigh : data->netWorkSet[n])
			{
				if (data->nodeInfo[neigh][0] == commIds[i])
				{
					int newNeigh = idToNew[neigh];
					int newN = idToNew[n];
					(*edges)[newNeigh].insert(newN);
					(*edges)[newN].insert(newNeigh);
				}

				int c1 = data->nodeInfo[n][0];
				int c2 = data->nodeInfo[neigh][0];

				commoe[c1].insert(c2);
				commie[c2].insert(c1);
			}
		}

		//sort(cnodes.begin(), cnodes.end());
		TempGraph* t = new TempGraph(newnodes, nodeAttributes, edgeAttributes, edges, edges, data->labelnum, &data->nodeLabels);
		t->nodeset = new unordered_set<int>(newnodes.begin(), newnodes.end());
		t->idMapping = cnodes;

		communityGraphs[commIds[i]] = t;
		communityGraphsVec[commIds[i]] = t;
	}

	pattern = new TempGraph(nodes, nodeAttributes, edgeAttributes, outedges, inedges, data->labelnum, nodeLabels);
	return;
	for (const auto& comm : communityGraphs)
	{
		int index = 0;
		int comm_id = comm.first;
		TempGraph* tg = comm.second;
		for (int i = 0; i < tg->nodes->size(); ++i)
		{	
			bool find = false;
			int n1 = (*tg->nodes)[i];
			int mapn1 = tg->idMapping[n1];
			for(int j = 0; j < i; ++j)
			{
				int n2 = (*tg->nodes)[j];
				int mapn2 = tg->idMapping[n2];
				if (equalInData.find(mapn2) == equalInData.end()
					|| data->nodeLabels[mapn1] != data->nodeLabels[mapn2])
					continue;

				unordered_set<int> temp1 = (*tg->outedges)[n1];
				unordered_set<int> temp2 = (*tg->outedges)[n2];
				temp1.insert(n1);
				temp1.insert(n2);
				temp2.insert(n1);
				temp2.insert(n2);
				bool in1 = true;
				bool in2 = true;
				if (temp1 != temp2)
					in2 = false;

				/*for (const auto& t1 : temp1)
				{
					if (temp2.find(t1) == temp2.end())
					{
						in2 = false;
						break;
					}
				}*/
				if (in2)
				{
					find = true;
					equalInData[mapn2].push_back(mapn1);
					break;
				}
				/*for (const auto& t2 : temp2)
				{
					if (temp1.find(t2) == temp1.end())
					{
						in1 = false;
						break;
					}
				}
				if (in1)
				{
					find = true;
					equalInData[mapn1] = equalInData[mapn2];
					equalInData[mapn1].push_back(mapn1);
					equalInData.erase(mapn2);
					break;
				}*/
			}
			if (!find)
			{
				equalInData[mapn1].push_back(mapn1);
			}
		}
		//cout << equalInData.size() << endl;
		//cout << equalInData[comm_id].size() << " " << tg->nodes->size() << endl;
	}
	cout << equalInData.size() << endl;
	equalBool = vector<int>(data->nodeNum + 1, 0);
	for (const auto& n : equalInData)
	{
		equalBool[n.first] = n.second.size();
		//int n1 = n.first;
		//for (const auto& n2 : equalInData[n1])
		//{
		//	equalTeam[n2] = n1;
		//}
	}
	cout << "finished" << endl;
	/*for (const auto& comm : communityGraphs)
	{
		TempGraph* tg = comm.second;
		for (int i = 0; i < tg->nodes->size(); ++i)
		{
			int n1 = (*tg->nodes)[i];
			vector<unordered_set<int>> saver;
			for (const auto& n2 : equalInData[n1])
			{
				unordered_set<int> diff;
				unordered_set<int> temp1 = (*tg->outedges)[n1];
				unordered_set<int> temp2 = (*tg->outedges)[n2];
				temp1.insert(n1);
				temp1.insert(n2);
				temp2.insert(n1);
				temp2.insert(n2);

				for (const auto& k : temp1)
				{
					if (temp2.find(k) == temp2.end())
					{
						diff.insert(k);
					}
				}
				saver.push_back(diff);
			}
			equalDiff[n1] = saver;
		}
	}*/
}

void Match::initCompleteMatchNodes()
{
	unordered_map<int, vector<int>> initvec;
	for (const auto& n : *pattern->nodes)
	{
		initvec[n].push_back(n);
		completeMatchPatternNodes[initvec[n]].insert(initvec[n]);
	}

	for (int i = 0; i < (*pattern->nodes).size(); i++)
	{
		int pid = (*pattern->nodes)[i];

		for (int j = i + 1; j < (*pattern->nodes).size(); j++)
		{
			int pid2 = (*pattern->nodes)[j];
			if (completeMatchPatternNodes[initvec[pid]] == completeMatchPatternNodes[initvec[pid2]])
				continue;

			if (matchType == 0)
			{
				if ((*pattern->outedges)[pid].size() != (*pattern->outedges)[pid2].size()
					|| (*pattern->inedges)[pid].size() != (*pattern->inedges)[pid2].size())
				{
					continue;
				}
			}
			else if (matchType == 1)
			{
				if ((*pattern->outedges)[pid].size() != (*pattern->outedges)[pid2].size())
				{
					continue;
				}
			}

			bool ok = true;

			for (const auto& n : (*pattern->outedges)[pid])
			{
				if (n != pid2 && (*pattern->outedges)[pid2].find(n) == (*pattern->outedges)[pid2].end())
				{
					ok = false;
					break;
				}
			}

			if (!ok)
			{
				continue;
			}

			if (matchType == 0)
			{
				for (const auto& n : (*pattern->inedges)[pid])
				{
					if (n != pid2 && (*pattern->inedges)[pid2].find(n) == (*pattern->inedges)[pid2].end())
					{
						ok = false;
						break;
					}
				}

				if (!ok)
				{
					continue;
				}
			}

			completeMatchPatternNodes[initvec[pid]].insert(initvec[pid2]);
			//completeMatchPatternNodes[initvec[pid2]].insert(initvec[pid]);
			//delete completeMatchPatternNodes[initvec[pid2]];
			completeMatchPatternNodes[initvec[pid2]].insert(initvec[pid]);
			equals[pid].insert(pid2);
			equals[pid2].insert(pid);
		}
	}

	int classNumber = 0;
	for (const auto& n : *pattern->nodes)
	{
		if (patternEqualClass.find(n) != patternEqualClass.end())
		{
			continue;
		}
		classNumber++;
		int node_id = n;
		for (const auto& c : completeMatchPatternNodes[initvec[node_id]])
		{
			for (const auto& cn : c)
			{
				patternEqualClass[cn] = classNumber;
			}
		}
	}

	string ans = "";
	unordered_map<int, int> mapper;
	unordered_map<int, unordered_map<int, bool>> symm;
	for (const auto& n : *pattern->nodes)
	{
		for (const auto& m : *pattern->nodes)
		{
			if (completeMatchPatternNodes[initvec[n]].find(initvec[m]) == completeMatchPatternNodes[initvec[n]].end())
			{
				int count = 0;
				vector<vector<int>*> boundary(pattern->nodenum + 1, NULL);
				boundary[n] = &initvec[m];
				boundary[m] = &initvec[n];
				
				//自同构接口 interface #1
				VF3StateSelf s(pattern, pattern, data->labelnum);
				s.nodeArea = &boundary;
				if (s.match())
				{
					symmetryNodes[initvec[n]].insert(initvec[m]);
				}
			}
		}
	}

}

void Match::handleExchange(unordered_map<string, vector<vector<int>>>& isomorphicList
	, map<vector<int>, string>& isomap)
{
	vector<int> current;
	for (const auto& n : *pattern->nodes)
	{
		current.push_back(n);
	}
	unordered_set<int> record;
	vector<int> temp;
	getAllMatchNodes(current, 0, temp, record, false);

	for (const auto& v : completeMatchPatternNodes[current])
	{
		//vector v
		bool canmatch = true;
		for (int i = 0; i < pattern->nodes->size(); ++i)
		{
			int n1 = (*pattern->nodes)[i];
			for (const auto& n2 : (*pattern->outedges)[n1])
			{
				if ((*pattern->outedges)[v[n1 - 1]].find(v[n2 - 1]) == (*pattern->outedges)[v[n1 - 1]].end())
				{
					canmatch = false;
					break;
				}
			}
			if (!canmatch)
				break;
		}
		if (canmatch)
		{
			displace.insert(v);
		}
	}

	schemes = vector<vector<int>>(displace.size(), vector<int>(pattern->nodes->size() + 1));
	int index = 0;
	for (const auto& d : displace)
	{
		for (int i = 0; i < d.size(); ++i)
		{
			schemes[index][d[i]] = i + 1;
		}
		index++;
	}

	current.clear();
	completeMatchPatternNodes.clear();
	retrivalPatterns(current, 0, false);

	/*map<vector<int>, set<vector<int>>>::iterator mit = completeMatchPatternNodes.begin();
	while (mit != completeMatchPatternNodes.end())
	{
		set<vector<int>>::iterator sit = mit->second.begin();
		while (sit != mit->second.end())
		{
			vector<int> nv(*sit);
			//sort(nv.begin(), nv.end());
			if (completeMatchRecord[mit->first].find(nv) != completeMatchRecord[mit->first].end())
			{
				//(completeMatchPatternNodes[mit->first]).erase(sit++);
				//continue;
			}
			completeMatchRecord[mit->first].insert(nv);
			sort(nv.begin(), nv.end());
			if (isomap[nv] != isomap[mit->first])
			//{
		//		(completeMatchPatternNodes[mit->first]).erase(sit++);
			//}
			//else
			//{
		//		sit++;
		//	}
		//}
		//handled.insert(mit->second);
	//	mit++;
//	}*/

	map<vector<int>, set<vector<int>>>::iterator mit = completeMatchPatternNodes.begin();
	while (mit != completeMatchPatternNodes.end())
	{
		set<vector<int>>::iterator sit = mit->second.begin();
		set<int> mitset = set<int>(mit->first.begin(), mit->first.end());
		while (sit != mit->second.end())
		{
			set<int> nv(sit->begin(), sit->end());
			completeSet[mitset].insert(nv);
			sit++;
		}
		//handled.insert(mit->second);
		mit++;
	}
}

void Match::handleMatchPattern(unordered_map<string, vector<vector<int>>>& isomorphicList
	, map<vector<int>, string>& isomap)
{
	vector<int> current;
	vector<unordered_set<int>> tempOut(pattern->nodenum + 1), tempIn(pattern->nodenum + 1);
	retrivalNodes(current, 0, isomorphicList, isomap, false, tempOut, tempIn);

	unordered_set<set<vector<int>>*> handled;
	map<vector<int>, set<vector<int>>>::iterator mit = completeMatchPatternNodes.begin();
	while (mit != completeMatchPatternNodes.end())
	{
		//if (handled.find(mit->second) != handled.end())
		//{
		//	mit++;
		//	continue;
		//}
		set<vector<int>>::iterator sit = mit->second.begin();
		while (sit != mit->second.end())
		{
			vector<int> nv(*sit);
			sort(nv.begin(), nv.end());
			if (completeMatchRecord[mit->first].find(nv) != completeMatchRecord[mit->first].end())
			{
				(completeMatchPatternNodes[mit->first]).erase(sit++);
				continue;
			}
			completeMatchRecord[mit->first].insert(nv);
			if (isomap[nv] != isomap[mit->first/*s*/])
			{
				(completeMatchPatternNodes[mit->first]).erase(sit++);
			}
			else
			{
				sit++;
			}
		}
		//handled.insert(mit->second);
		mit++;
	}

	mit = completeMatchPatternNodes.begin();
	while (mit != completeMatchPatternNodes.end())
	{
		set<vector<int>>::iterator sit = mit->second.begin();
		set<int> mitset = set<int>(mit->first.begin(), mit->first.end());
		while (sit != mit->second.end())
		{
			set<int> nv(sit->begin(), sit->end());
			completeSet[mitset].insert(nv);
			sit++;
		}
		//handled.insert(mit->second);
		mit++;
	}
}

void Match::retrivalNodes(vector<int>& current, int pos, unordered_map<string, vector<vector<int>>>& isomorphicList
	, map<vector<int>, string>& isomap, bool added, vector<unordered_set<int>>& tempOut
	, vector<unordered_set<int>>& tempIn)
{
	if (added)
	{
		if (current.size() >= 1)
		{
			unordered_set<int> record;
			vector<int> temp;
			getAllMatchNodes(current, 0, temp, record, false);
		}

		submapNodeOutEdge[current] = tempOut;
		submapNodeInEdge[current] = tempIn;

		TempGraph* temp = new TempGraph(&current, pattern->nodeAttributes, pattern->edgeAttributes, &submapNodeOutEdge[current], &submapNodeInEdge[current], data->labelnum, &pattern->nodeLabels);

		bool succeed = false;
		for (const auto& strmatch : stringMatchModel)
		{
			if (current.size() != (*strmatch.second->nodes).size())
			{
				continue;
			}

			string ans = "";
			unordered_map<int, int> mapper;

			int count = 0;
			//完全匹配接口 interface #2
			VF2StateSub* s = new VF2StateSub(temp, strmatch.second);
			match_sub(s, &count, ans, mapper, 0);
			delete s;

			if (!ans.empty())
			{
				isomorphicList[strmatch.first].push_back(current);
				isomap[current] = strmatch.first;
				
				succeed = true;
				break;
			}
		}

		if (!succeed)
		{
			string ans = "";
			for (const auto& c : current)
			{
				ans += __to_string(c);
				ans += "_";
			}
			//unordered_map<int, int> mapper;

			TempGraph* t = new TempGraph(current, pattern->nodeAttributes, pattern->edgeAttributes, &submapNodeOutEdge[current], &submapNodeInEdge[current], data->labelnum, &pattern->nodeLabels);
			stringMatchModel[ans] = t;

			isomorphicList[ans].push_back(current);
			isomap[current] = ans;

		}
	}

	if (pos >= (*pattern->nodes).size())
	{
		return;
	}

	retrivalNodes(current, pos + 1, isomorphicList, isomap, false, tempOut, tempIn);

	vector<unordered_set<int>> saveIn = tempIn;
	vector<unordered_set<int>> saveOut = tempOut;

	//未考虑自环
	for (int i = 0; i < current.size(); i++)
	{
		if (pattern->HasEdge(current[i], (*pattern->nodes)[pos]))
		{
			saveOut[current[i]].insert((*pattern->nodes)[pos]);
			//if (matchType == 0)
			{
				saveIn[(*pattern->nodes)[pos]].insert(current[i]);
			}
		}
		if (pattern->HasEdge((*pattern->nodes)[pos], current[i]))
		{
			saveOut[(*pattern->nodes)[pos]].insert(current[i]);
			//if (matchType == 0)
			{
				saveIn[current[i]].insert((*pattern->nodes)[pos]);
			}
		}
	}

	current.push_back((*pattern->nodes)[pos]);
	retrivalNodes(current, pos + 1, isomorphicList, isomap, true, saveOut, saveIn);
	current.pop_back();
}

void Match::retrivalPatterns(vector<int>& current, int pos, bool added)
{
	if (added)
	{
		if (current.size() >= 1)
		{
			vector<int> t(current.size());
			for (int i = 0; i < schemes.size(); ++i)
			{
				for (int j = 0; j < current.size(); ++j)
				{
					t[j] = schemes[i][current[j]];
				}
				sort(t.begin(), t.end());
				completeMatchPatternNodes[current].insert(t);
			}
		}
	}

	if (pos >= (*pattern->nodes).size())
	{
		return;
	}

	retrivalPatterns(current, pos + 1, false);

	current.push_back((*pattern->nodes)[pos]);
	retrivalPatterns(current, pos + 1, true);
	current.pop_back();
}

void Match::getAllMatchNodes(vector<int>& currents, int pos, vector<int>& t, unordered_set<int>& record, bool hasSymm)
{
	if (pos >= currents.size())
	{
		if (completeMatchPatternNodes.find(currents) != completeMatchPatternNodes.end()
			&& completeMatchPatternNodes[currents].find(t) != completeMatchPatternNodes[currents].end())
		{
			return;
		}
		if (hasSymm)
		{
			unordered_map<int, int> mapper;
			for (int i = 0; i < currents.size(); i++)
			{
				mapper[currents[i]] = t[i];
			}

			unordered_set<int> nodes, currentNodes, tNodes;
			bool isAll = false;
			bool isSameNeighs = true;

			for (const auto& c : currents)
			{
				//nodes.insert(c);
				currentNodes.insert(c);
			}
			for (const auto& c : t)
			{
				//nodes.insert(c);
				tNodes.insert(c);
			}

			for (int i = 0; i < currents.size(); i++)
			{
				unordered_set<int> currentOutNeighs, currentOutNeighs2, currentInNeighs, currentInNeighs2, tOutNeighs, tOutNeighs2, tInNeighs, tInNeighs2;

				//currentOutNeighs.insert(mapper[currents[i]]);
				for (const auto& out : (*pattern->outedges)[currents[i]])
				{
					if (out == currents[i] || out == t[i])
					{
						continue;
					}
					if (mapper.find(out) != mapper.end())
					{
						currentOutNeighs.insert(mapper[out]);
					}
					else
					{
						currentOutNeighs.insert(out);
					}
					currentOutNeighs2.insert(out);
				}

				/*if (mapper.find(t[i]) != mapper.end())
				{
				tOutNeighs.insert(mapper[t[i]]);
				}
				else*/
				{
					//tOutNeighs.insert(t[i]);
				}
				for (const auto& out : (*pattern->outedges)[t[i]])
				{
					if (out == currents[i] || out == t[i])
					{
						continue;
					}
					if (mapper.find(out) != mapper.end())
					{
						tOutNeighs2.insert(mapper[out]);
					}
					else
					{
						tOutNeighs2.insert(out);
					}
					tOutNeighs.insert(out);
				}
				if (currentOutNeighs != tOutNeighs && currentOutNeighs2 != tOutNeighs2 && currentOutNeighs2 != tOutNeighs)
				{
					isSameNeighs = false;
					break;
				}

				//currentInNeighs.insert(mapper[currents[i]]);
				for (const auto& in : (*pattern->inedges)[currents[i]])
				{
					if (in == currents[i] || in == t[i])
					{
						continue;
					}
					if (mapper.find(in) != mapper.end())
					{
						currentInNeighs.insert(mapper[in]);
					}
					else
					{
						currentInNeighs.insert(in);
					}
					currentInNeighs2.insert(in);
				}

				/*if (mapper.find(t[i]) != mapper.end())
				{
				tInNeighs.insert(mapper[t[i]]);
				}
				else*/
				{
					//tInNeighs.insert(t[i]);
				}
				for (const auto& in : (*pattern->inedges)[t[i]])
				{
					if (in == currents[i] || in == t[i])
					{
						continue;
					}
					if (mapper.find(in) != mapper.end())
					{
						tInNeighs2.insert(mapper[in]);
					}
					else
					{
						tInNeighs2.insert(in);
					}
					tInNeighs.insert(in);
				}

				if (currentInNeighs != tInNeighs && currentInNeighs2 != tInNeighs2 && currentInNeighs2 != tInNeighs)
				{
					isSameNeighs = false;
					break;
				}
			}

			if (isSameNeighs)
			{
				if (currentNodes == tNodes)
				{
					//if (is_sorted(t.begin(), t.end()))
					{
						//if (completeMatchPatternNodes.find(currents) == completeMatchPatternNodes.end())
						//{
						//completeMatchPatternNodes[currents] = new set<vector<int>>();
						//}
						completeMatchPatternNodes[currents].insert(t);
						completeMatchPatternNodes[t].insert(currents);// = completeMatchPatternNodes[currents];
					}
				}
				else
				{
					//if (completeMatchPatternNodes.find(currents) == completeMatchPatternNodes.end())
					//{
					//	completeMatchPatternNodes[currents] = new set<vector<int>>();
					//}
					completeMatchPatternNodes[currents].insert(t);
					if (is_sorted(t.begin(), t.end()))
					{
						completeMatchPatternNodes[t].insert(currents);// = completeMatchPatternNodes[currents];
					}
					//completeMatchPatternNodes[currents]->insert(t);
				}
			}
			/*if (nodes.size() == patternGraph->nodes.size())
			{
			isAll = true;
			}
			if (isAll || isSameNeighs)
			{
			if (currentNodes == tNodes)
			{
			if (is_sorted(t.begin(), t.end()))
			{
			completeMatchPatternNodes[currents].insert(t);
			}
			}
			else
			{
			completeMatchPatternNodes[currents].insert(t);
			}
			}*/
		}
		else
		{
			unordered_map<int, vector<int>> equalClassVector;
			for (int i = 0; i < t.size(); i++)
			{
				equalClassVector[patternEqualClass[t[i]]].push_back(t[i]);
			}
			/*for (const auto& e : equalClassVector)
			{
				if (!is_sorted(e.second.begin(), e.second.end()))
				{
					return;
				}
			}*/

			//if (completeMatchPatternNodes.find(currents) == completeMatchPatternNodes.end())
			//{
			//	completeMatchPatternNodes[currents] = new set<vector<int>>();
			//}
			completeMatchPatternNodes[currents].insert(t);
			if (is_sorted(t.begin(), t.end()))
			{
				completeMatchPatternNodes[t].insert(currents);// = completeMatchPatternNodes[currents];
			}
			//completeMatchPatternNodes[currents]->insert(t);
		}

		return;
	}

	vector<int> temp(1, currents[pos]);

	for (const auto& ns : completeMatchPatternNodes[temp])
	{
		for (const auto& n : ns)
		{
			if (record.find(n) != record.end())
			{
				continue;
			}
			t.push_back(n);
			record.insert(n);
			getAllMatchNodes(currents, pos + 1, t, record, hasSymm);
			t.pop_back();
			record.erase(n);
		}
	}

	for (const auto& ns : symmetryNodes[temp])
	{
		for (const auto& n : ns)
		{
			if (record.find(n) != record.end())
			{
				continue;
			}
			t.push_back(n);
			record.insert(n);
			getAllMatchNodes(currents, pos + 1, t, record, true);
			t.pop_back();
			record.erase(n);
		}
	}
}

void Match::initOrderTree()
{
	for (auto& c : completeMatchPatternNodes)
	{
		if (c.second.begin()->size() > 1)
		{
			orderTree.insert(set<int>(c.second.begin()->begin(), c.second.begin()->end()));
		}
		else
		{
			orderTree1D.insert((*c.second.begin())[0]);
		}

		int minlocal = *c.first.begin();
		set<vector<int>>::iterator record = c.second.end();
		set<vector<int>>::iterator cit = c.second.begin();
		while(cit != c.second.end())
		{
			if ((*cit)[0] == minlocal)
			{
				if (record == c.second.end())
					record = cit;
				else
				{
					for (int i = 0; i < (*cit).size(); ++i)
					{
						if ((*record)[i] >(*cit)[i])
						{
							record = cit;
						}
					}
				}
			}

			cit++;
		}

		localMinTree.insert(set<int>(record->begin(), record->end()));
	}
}

int Match::GoMatch_Turbo()
{
	clock_t start, end;
	start = clock();

	TurboMatch tm;
	tm.q = pattern;
	tm.g = new TempGraph(data->node_ids, NULL, NULL, &(data->netWorkSet), &(data->netWorkSet), data->labelnum, &data->nodeLabels);
	tm.data = this->data;
	tm.gm = this;
	tm.storeType = 0;
	tm.communityGraphs = &communityGraphsVec;
	tm.init();
	tm.ranks = new int*[pattern->nodenum];
	for (int pn = 0; pn < pattern->nodenum; ++pn)
	{
		tm.ranks[pn] = new int[pattern->nodenum];
	}
	bool candups = false;
	ansnum = tm.TurboISO(tm.q, tm.g, candups, 0);

	end = clock();
	cout << "Time: " << (double)(end - start) / CLOCKS_PER_SEC << endl;

	//ans.clear();

	//cout << "super match over" << endl;

	/*int sumc = 0;
	int index = 0;
	cout << "start" << endl;
	for (const auto& n : tans)
	{
	cout << index++ << " " << n.size() << endl;
	sumc += n.size();
	for (const auto& m : n)
	{
	ans.push_back(m);
	}
	}
	//cout << "blocktime: " << storage.blocktime << endl;*/
	cout << "sumc: " << ansnum << endl;
	//cout << usefulCS << " " << uselessCS << " " << uselessCut2 << " " << uselessUntrivial << endl;

	// logger.close();
	return ansnum;
}

int Match::GoMatch_Turbo_comm()
{
	clock_t start, end;
	start = clock();

	completeMatchPatternNodes.clear();
	initCompleteMatchNodes();

	unordered_map<string, vector<vector<int>>> isomorphicList;
	map<vector<int>, string> isomap;
	handleExchange(isomorphicList, isomap);
	//handleMatchPattern(isomorphicList, isomap);
	//initOrderTree();
	
	//cout << "init over" << endl;
	vector<vector<vector<int>>> tans(1, vector<vector<int>>());

	int count[16] = { 0 };
	int pc = 0;

	vector<vector<int>> equalq(pattern->nodenum + 1, vector<int>(pattern->nodenum + 1, 0));
	NECTree q_prime;
	TurboMatch tempm;
	vector<vector<int>> NECV;
	vector<int> qnodes = *pattern->nodes;
	tempm.FindNEC(&NECV, &qnodes, pattern);
	//#pragma omp parallel for schedule(dynamic) if(ISPARALLEL)
	for (int i = 0; i < NECV.size(); i++)
	{
		//unordered_set<int>* s = new unordered_set<int>(NECV[i].begin(), NECV[i].end());
		for (const auto& n : NECV[i])
		{
			for(const auto& n2 : NECV[i])
				equalq[n][n2] = 1;
		}
	}

	int s = 0;
	//for (int i = 0; i < 16; ++i)
	//	s += count[i];
	//cout << "sum: " << s <<  " " << tans[0].size() << " " << tans[1].size() << " " << tans[2].size() << " " << tans[3].size() << endl;
	// cout << s << endl;
	ansnum = 0;
	//return 0;
	vector<map<int, vector<int>>> supermatch;

	int c = 0;
	TempGraph commGraph(commIds, NULL, NULL, &commoe, &commie, data->labelnum, &data->nodeLabels);
	//可重复的子图匹配 interface #3
	TurboMatch tm;
	tm.q = pattern;
	tm.g = &commGraph;
	tm.data = this->data;
	tm.gm = this;
	tm.storeType = 2;
	tm.superans = &supermatch;
	tm.tans = &tans;
	tm.isomap = &isomap;
	tm.communityGraphs = &communityGraphsVec;
	tm.originalgraph = new TempGraph(data->node_ids, NULL, NULL, &(data->netWorkSet), &(data->netWorkSet), data->labelnum, &data->nodeLabels);
	tm.equalq = &equalq;
	bool candups = true;
	tm.init(true);
	vector<NECTree> qs(pattern->nodenum + 1);
	for (int i = 1; i < qs.size(); ++i)
	{
		NECTree temp;
		tm.RewriteToNECTree(pattern, i, &temp);
		qs[i] = temp;
	}
	tm.q_primes = &qs;
	tm.TurboISOSuper(tm.q, tm.g, candups);

	end = clock();
	cout << "Time: " << (double)(end - start) / CLOCKS_PER_SEC << endl;

	//ans.clear();

	//cout << "super match over" << endl;

	/*int sumc = 0;
	int index = 0;
	cout << "start" << endl;
	for (const auto& n : tans)
	{
	cout << index++ << " " << n.size() << endl;
	sumc += n.size();
	for (const auto& m : n)
	{
	ans.push_back(m);
	}
	}
	//cout << "blocktime: " << storage.blocktime << endl;*/
	cout << "sumc: " << s + ansnum << endl;
	cout << usefulCS << " " << uselessCS << " " << uselessCut2 << " " << uselessUntrivial << " " << uselessDouble << " " << samecounter << endl;

	// logger.close();
	return ansnum + s;
}

bool Match::getAllInPatternCompleteMatch(map<int, vector<int>>& supermatch, map<int, int>& supermatchmap, string& mystr, map<int, vector<int>>::iterator& sit, vector<map<int, int>>& allmaps, map<int, int>& currentMap, unordered_set<int>& usednodes)
{
	if (sit == supermatch.end())
	{
		bool issmallest = true;
		string thisstr = "";
		map<int, int> newmatch;
		for (const auto& a : currentMap)
		{
			newmatch[a.second] = a.first;
		}
		for (const auto& a : newmatch)
		{
			string str = __to_string(supermatchmap[a.second]);
			thisstr += ('A' + str.size());
			thisstr += str + " ";
		}
		if (thisstr < mystr)
		{
			return false;
		}
		else
		{
			allmaps.push_back(currentMap);
			//allmaps.insert(currentMap);
			return true;
		}
	}

	int comm_id = sit->first;
	map<int, vector<int>>::iterator nextit = ++sit;
	sit--;

	for (const auto& v : completeMatchPatternNodes[sit->second])
	{
		bool check = true;
		for (int i = 0; i < v.size(); i++)
		{
			if (usednodes.find(v[i]) != usednodes.end())
			{
				check = false;
				break;
			}

			currentMap[sit->second[i]] = v[i];
		}
		if (!check)
		{
			continue;
		}

		usednodes.insert(v.begin(), v.end());

		if (!getAllInPatternCompleteMatch(supermatch, supermatchmap, mystr, nextit, allmaps, currentMap, usednodes))
		{
			return false;
		}

		for (int i = 0; i < v.size(); i++)
		{
			currentMap[sit->second[i]] = -1;
			usednodes.erase(v[i]);
		}
	}

	return true;
}

bool Match::getCompleteMatch(int* supermatchmap, vector<int>& allmaps, unordered_set<string>& record)
{
	for(int i = 0; i < schemes.size(); ++i)
	{
		bool smaller = false;
		string thisstr = "";
		for (int j = 1; j < schemes[i].size(); ++j)
		{
			if (!smaller)
			{
				if (supermatchmap[schemes[i][j]] < supermatchmap[j])
					return false;
				else if (supermatchmap[schemes[i][j]] > supermatchmap[j])
				{
					smaller = true;
				}
			}
			//string str = to_string(supermatchmap[schemes[i][j]]);
			thisstr += supermatchmap[schemes[i][j]];
			//thisstr += str + " ";
		}
		/*if (thisstr < mystr)
		{
			//cout << thisstr << " " << mystr << endl;
			//system("pause");
			return false;
		}
		else
		{
			if (record.find(thisstr) == record.end())
			{
				allmaps.push_back(i);
				record.insert(thisstr);
			}
			//allmaps.insert(currentMap);
		}*/
		if (record.find(thisstr) == record.end())
		{
			allmaps.push_back(i);
			record.insert(thisstr);
		}
	}

	return true;
}

bool Match::match_sub(VF2StateSub* s, int* pcount, string& ans, unordered_map<int, int>& mapper, int nextn1, bool iswrite)
{
	if (s->IsGoal())
	{
		++*pcount;
		int n = s->CoreLen();
		s->GetCoreSet(ans, mapper, iswrite);
		return true;
	}

	if (s->IsDead())
	{
		return false;
	}

	int n1 = -1, n2 = -1;
	while (s->NextPair(&n1, &n2, n1, n2))
	{
		if (s->IsFeasiblePair(n1, n2))
		{
			VF2StateSub* s1 = s->Clone();
			s1->AddPair(n1, n2);
			if (match_sub(s1, pcount, ans, mapper, nextn1 + 1, iswrite))
			{
				s1->BackTrack();
				delete s1;
				return true;
			}
			else
			{
				s1->BackTrack();
				delete s1;
			}
		}
	}

	return false;
}

bool Match::vf3_match(VF3State &s, int *pn)
{
	if (s.IsGoal())
	{
		++*pn;
		//int n = s.CoreLen();
		//s.GetCoreSet(c2);
		return false;
	}

	if (s.IsDead())
		return false;

	int n1 = -1, n2 = -1;
	
	while (s.NextPair(&n1, &n2, n1, n2))
	{
		if (s.IsFeasiblePair(n1, n2))
		{
			VF3State s1(s);
			s1.AddPair(n1, n2);
			if (vf3_match(s1, pn))
			{
				return true;
			}
		}
	}
	return false;
}

int Match::GoMatch_vf3()
{
	clock_t start, end;
	start = clock();

	VF3NodeSorter sorter(data);
	vector<int> sorted = sorter.SortNodes(pattern);

	int pnum = pattern->nodes->size();
	int gnum = data->node_ids.size();
	
	VF3State s0(pattern, data, this, data->labelnum, sorted.data());
	int n = 0;

	vf3_match(s0, &n);

	end = clock();
	cout << "Time: " << (double)(end - start) / CLOCKS_PER_SEC << endl;
	cout << n << endl;

	return 0;
}

int Match::GoMatch_vf3_comm()
{
	clock_t start, end;
	start = clock();

	completeMatchPatternNodes.clear();
	initCompleteMatchNodes();

	unordered_map<string, vector<vector<int>>> isomorphicList;
	map<vector<int>, string> isomap;
	handleExchange(isomorphicList, isomap);
	//handleMatchPattern(isomorphicList, isomap);
	//initOrderTree();

	//cout << "init over" << endl;
	vector<vector<vector<int>>> tans(1, vector<vector<int>>());

	int count[16] = { 0 };
	int pc = 0;

	vector<unordered_set<int>*> equalq(pattern->nodenum + 1, NULL);
	NECTree q_prime;
	TurboMatch tempm;
	vector<vector<int>> NECV;
	vector<int> qnodes = *pattern->nodes;
	tempm.FindNEC(&NECV, &qnodes, pattern);
	//#pragma omp parallel for schedule(dynamic) if(ISPARALLEL)
	for (int i = 0; i < NECV.size(); i++)
	{
		unordered_set<int>* s = new unordered_set<int>(NECV[i].begin(), NECV[i].end());
		for (const auto& n : NECV[i])
		{
			equalq[n] = s;
		}
	}

	int s = 0;
	for (int i = 0; i < 16; ++i)
		s += count[i];
	//cout << "sum: " << s <<  " " << tans[0].size() << " " << tans[1].size() << " " << tans[2].size() << " " << tans[3].size() << endl;
	cout << s << endl;
	ansnum = 0;
	//return 0;
	vector<map<int, vector<int>>> supermatch;

	int c = 0;
	TempGraph commGraph(commIds, NULL, NULL, &commoe, &commie, data->labelnum, &data->nodeLabels);
	//可重复的子图匹配 interface #3

	vector<vector<int>> commNodeLabels(commIds.size() + 1, vector<int>(data->labelnum + 1, 0));
	for (int c = 1; c < data->communityNodes.size(); ++c)
	{
		for (const auto& n : data->communityNodes[c])
		{
			commNodeLabels[c][data->nodeLabels[n]] = 1;
		}
	}
	
	VF3StateSuper state(pattern, &commGraph, this, data->labelnum);
	state.data = this->data;
	state.communityGraphs = &communityGraphsVec;
	state.originalgraph = new TempGraph(data->node_ids, NULL, NULL, &(data->netWorkSet), &(data->netWorkSet), data->labelnum, &data->nodeLabels);
	state.equalq = &equalq;
	state.commNodeLabels = &commNodeLabels;
	state.recin = new VF3StateIn(pattern, NULL, this, data->labelnum);
	state.recbound = new VF3StateBound(pattern, state.originalgraph, this, data->labelnum);
	state.recbound->communityGraphs = state.communityGraphs;
	state.recbound->data = data;
	state.match();

	end = clock();
	cout << "Time: " << (double)(end - start) / CLOCKS_PER_SEC << endl;

	cout << "sumc: " << s + ansnum << endl;
	cout << usefulCS << " " << uselessCS << " " << uselessCut2 << " " << uselessUntrivial << endl;

	// logger.close();
	return ansnum + s;
}

