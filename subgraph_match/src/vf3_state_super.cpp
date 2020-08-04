#include "vf3_state_super.h"

static bool cmpD(const DegreePos& a, const DegreePos& b)
{
	return a.degree < b.degree;
}

void VF3StateSuper::print_terminal(int c) {
	std::cout << "\nClass: " << c << " Core_len: " << core_len_c[c];
	std::cout << " t1both_len: " << t1both_len_c[core_len][c] << " t2both_len " << t2both_len_c[c];
	std::cout << " t1out_len: " << t1out_len_c[core_len][c] << " t2out_len " << t2out_len_c[c];
	std::cout << " t1in_len: " << t1in_len_c[core_len][c] << " t2in_len " << t2in_len_c[c];

}


VF3StateSuper::VF3StateSuper(TempGraph *ag1, TempGraph *ag2, Match* m, int nclass, int* order)
{
	//assert(class_1 != NULL && class_2 != NULL);

	//VF3State::instance_count = 1;
	g1 = ag1;
	g2 = ag2;
	n1 = g1->nodenum;
	n2 = g2->nodenum;
	gm = m;

	this->order = order;
	//this->class_1 = class_1;
	//this->class_2 = class_2;
	this->classes_count = nclass;

	core_len = orig_core_len = 0;
	t2both_len = t2in_len = t2out_len = 0;

	//Creazione degli insiemi
	t1both_len = new int[n1 + 1];
	t1in_len = new int[n1 + 1];
	t1out_len = new int[n1 + 1];

	termin1 = (int*)calloc(n1, sizeof(int));
	termout1 = (int*)calloc(n1, sizeof(int));
	new1 = (int*)calloc(n1, sizeof(int));

	t1both_len_c = (int**)malloc((n1 + 1) * sizeof(int*));
	t1in_len_c = (int**)malloc((n1 + 1) * sizeof(int*));
	t1out_len_c = (int**)malloc((n1 + 1) * sizeof(int*));


	termin1_c = (int**)malloc(n1 * sizeof(int*));
	termout1_c = (int**)malloc(n1 * sizeof(int*));
	new1_c = (int**)malloc(n1 * sizeof(int*));

	core_len_c = (int*)calloc(classes_count, sizeof(int));
	t2both_len_c = (int*)calloc(classes_count, sizeof(int));
	t2in_len_c = (int*)calloc(classes_count, sizeof(int));
	t2out_len_c = (int*)calloc(classes_count, sizeof(int));
	termout2_c = new int[classes_count];
	termin2_c = new int[classes_count];
	new2_c = new int[classes_count];

	added_node1 = -1;

	core_1 = new int[n1 + 1];
	core_2 = new int[n2 + 1];
	in_2 = new int[n2 + 1];
	out_2 = new int[n2 + 1];
	dir = new node_dir_t[n1 + 1];
	predecessors = new int[n1 + 1];
	share_count = new long;

	int i;
	for (i = 0; i <= n1; i++)
	{
		if (i<n1) {
			termin1_c[i] = (int*)calloc(classes_count, sizeof(int));
			termout1_c[i] = (int*)calloc(classes_count, sizeof(int));
			new1_c[i] = (int*)calloc(classes_count, sizeof(int));
		}
		core_1[i] = -1;
		t1both_len_c[i] = (int*)calloc(classes_count, sizeof(int));
		t1in_len_c[i] = (int*)calloc(classes_count, sizeof(int));
		t1out_len_c[i] = (int*)calloc(classes_count, sizeof(int));
	}

	for (i = 1; i <= n2; i++)
	{
		core_2[i] = -1;
		in_2[i] = 0;
		out_2[i] = 0;
	}

	//ComputeFirstGraphTraversing();
	*share_count = 1;
	recin = NULL;
	recbound = NULL;
}


VF3StateSuper::VF3StateSuper(const VF3StateSuper &state)
{
	g1 = state.g1;
	g2 = state.g2;
	n1 = state.n1;
	n2 = state.n2;
	gm = state.gm;
	data = state.data;
	communityGraphs = state.communityGraphs;
	originalgraph = state.originalgraph;
	equalq = state.equalq;
	recin = state.recin;
	recbound = state.recbound;
	commNodeLabels = state.commNodeLabels;

	order = state.order;
	//class_1 = state.class_1;
	//class_2 = state.class_2;
	classes_count = state.classes_count;
	//VF3State::instance_count++;

	core_len = orig_core_len = state.core_len;

	t1in_len = state.t1in_len;
	t1out_len = state.t1out_len;
	t1both_len = state.t1both_len;

	t2in_len = state.t2in_len;
	t2out_len = state.t2out_len;
	t2both_len = state.t2both_len;

	core_len_c = state.core_len_c;
	t1both_len_c = state.t1both_len_c;
	t2both_len_c = state.t2both_len_c;
	t1in_len_c = state.t1in_len_c;
	t2in_len_c = state.t2in_len_c;
	t1out_len_c = state.t1out_len_c;
	t2out_len_c = state.t2out_len_c;

	termout1_c = state.termout1_c;
	termout2_c = state.termout2_c;
	termin1_c = state.termin1_c;
	termin2_c = state.termin2_c;
	new1_c = state.new1_c;
	new2_c = state.new2_c;

	termin1 = state.termin1;
	termout1 = state.termout1;
	new1 = state.new1;

	added_node1 = -1;

	core_1 = state.core_1;
	core_2 = state.core_2;
	in_2 = state.in_2;
	out_2 = state.out_2;
	dir = state.dir;
	predecessors = state.predecessors;
	share_count = state.share_count;

	++ *share_count;

}


VF3StateSuper::~VF3StateSuper()
{

	if (-- *share_count > 0)
		BackTrack();

	if (*share_count == 0)
	{
		delete[] core_1;
		delete[] core_2;
		delete[] in_2;
		delete[] out_2;
		delete[] dir;
		delete[] predecessors;
		delete[] t1both_len;
		delete[] t1in_len;
		delete[] t1out_len;
		delete[] termin1;
		delete[] termout1;
		delete[] new1;

		for (int i = 0; i <= n1; i++) {
			delete[] t1both_len_c[i];
			delete[] t1in_len_c[i];
			delete[] t1out_len_c[i];
			if (i< n1) {
				delete[] termin1_c[i];
				delete[] termout1_c[i];
				delete[] new1_c[i];
			}
		}

		delete[] t1both_len_c;
		delete[] t1in_len_c;
		delete[] t1out_len_c;
		delete[] termin1_c;
		delete[] termout1_c;
		delete[] new1_c;
		delete[] t2both_len_c;
		delete[] t2in_len_c;
		delete[] t2out_len_c;
		delete[] core_len_c;
		delete[] termin2_c;
		delete[] termout2_c;
		delete[] new2_c;

		delete share_count;
	}
}

void VF3StateSuper::UpdateTerminalSetSize(int node, int level, bool* in_1, bool* out_1, bool* inserted) {
	int i, neigh, c_neigh;
	int in1_count, out1_count;

	//Updating Terminal set size count And degree
	in1_count = (*g1->inedges)[node].size();
	out1_count = (*g1->outedges)[node].size();

	//Updating Inner Nodes not yet inserted
	//for (i = 0; i < in1_count; i++)
	//{
	for (const auto& neigh : (*g1->inedges)[node])
	{
		//Getting Neighborhood
		//neigh = g1->GetInEdge(node, i);
		c_neigh = g1->nodeLabels[neigh];

		if (!inserted[neigh])
		{
			if (in_1[neigh]) {
				termin1[level]++;
				termin1_c[level][c_neigh]++;
			}
			if (out_1[neigh]) {
				termout1[level]++;
				termout1_c[level][c_neigh]++;
			}
			if (!in_1[neigh] && !out_1[neigh]) {
				new1[level]++;
				new1_c[level][c_neigh]++;
			}
		}
	}

	//Updating Outer Nodes not yet insered
	//for (i = 0; i < out1_count; i++)
	for (const auto& neigh : (*g1->outedges)[node])
	{
		//Getting Neighborhood
		//neigh = g1->GetOutEdge(node, i);
		c_neigh = g1->nodeLabels[neigh];
		if (!inserted[neigh])
		{
			if (in_1[neigh]) {
				termin1[level]++;
				termin1_c[level][c_neigh]++;
			}
			if (out_1[neigh]) {
				termout1[level]++;
				termout1_c[level][c_neigh]++;
			}
			if (!in_1[neigh] && !out_1[neigh]) {
				new1[level]++;
				new1_c[level][c_neigh]++;
			}
		}
	}
}


//Provare ad avere in1 ed ou1 predeterminati, senza doverlo calcolare ad ogni iterazione
//La loro dimensione ad ogni livello dell'albero di ricerca e' predeterminato
//In questo modo mi basta conoscere solo l'ordine di scelta e la dimensione di in1 ed out1
void VF3StateSuper::ComputeFirstGraphTraversing() {
	//The algorithm start with the node with the maximum degree
	int depth, i;
	int node;	//Current Node
	int node_c; //Class of the current node
	bool* inserted = new bool[n1 + 1];
	bool *in, *out; //Internal Terminal Set used for updating the size of
	in = new bool[n1 + 1];
	out = new bool[n1 + 1];

	//Init vectors and variables
	node = 0;
	node_c = 0;

	t1in_len[0] = 0;
	t1out_len[0] = 0;
	t1both_len[0] = 0;

	for (i = 1; i <= n1; i++)
	{
		in[i] = false;
		out[i] = false;
		dir[i] = NODE_DIR_NONE;
		inserted[i] = false;
		predecessors[i] = -1;
	}

	/* Following the imposed node order */
	for (depth = 0; depth < n1; depth++)
	{
		node = order[depth];
		node_c = g1->nodeLabels[node];
		inserted[node] = true;

		UpdateTerminalSetSize(node, depth, in, out, inserted);

		//Updating counters for next step
		t1in_len[depth + 1] = t1in_len[depth];
		t1out_len[depth + 1] = t1out_len[depth];
		t1both_len[depth + 1] = t1both_len[depth];
		for (int j = 0; j < classes_count; j++)
		{
			t1in_len_c[depth + 1][j] = t1in_len_c[depth][j];
			t1out_len_c[depth + 1][j] = t1out_len_c[depth][j];
			t1both_len_c[depth + 1][j] = t1both_len_c[depth][j];
		}
		//Inserting the node
		//Terminal set sizes depends on the depth
		// < depth non sono nell'insieme
		// >= depth sono nell'insieme
		if (!in[node])
		{
			in[node] = true;
			t1in_len[depth + 1]++;
			t1in_len_c[depth + 1][node_c]++;
			if (out[node]) {
				t1both_len[depth + 1]++;
				t1both_len_c[depth + 1][node_c]++;
			}
		}

		if (!out[node])
		{
			out[node] = true;
			t1out_len[depth + 1]++;
			t1out_len_c[depth + 1][node_c]++;
			if (in[node]) {
				t1both_len[depth + 1]++;
				t1both_len_c[depth + 1][node_c]++;
			}
		}

		//Updating terminal sets
		int i, other, other_c;
		other_c = -1;
		//int insize = g1->inNetWorkSet[node].size();

		for (const auto& other : (*g1->inedges)[node])
			//for (i = 0; i<insize; i++)
		{
			//other = g1->GetInEdge(node, i);
			if (!in[other])
			{
				other_c = g1->nodeLabels[other];
				in[other] = true;
				t1in_len[depth + 1]++;
				t1in_len_c[depth + 1][other_c]++;
				if (!inserted[other])
				{
					//dir[other] = NODE_DIR_IN;
					if (predecessors[other] == -1)
					{
						dir[other] = NODE_DIR_IN;
						predecessors[other] = node;
					}
				}
				if (out[other]) {
					t1both_len[depth + 1]++;
					t1both_len_c[depth + 1][other_c]++;
					//if(!inserted[other])
					//dir[other] = NODE_DIR_BOTH;
				}
			}
		}

		for (const auto& other : (*g1->outedges)[node])
			//for (i = 0; i<g1->OutEdgeCount(node); i++)
		{
			//other = g1->GetOutEdge(node, i);
			if (!out[other])
			{
				other_c = g1->nodeLabels[other];
				out[other] = true;
				t1out_len[depth + 1]++;
				t1out_len_c[depth + 1][other_c]++;
				if (!inserted[other])
				{
					//dir[other] = NODE_DIR_OUT;
					if (predecessors[other] == -1)
					{
						predecessors[other] = node;
						dir[other] = NODE_DIR_OUT;
					}
				}
				if (in[other]) {
					t1both_len[depth + 1]++;
					t1both_len_c[depth + 1][other_c]++;
					//if(!inserted[other])
					//dir[other] = NODE_DIR_BOTH;
				}
			}
		}

	}

	delete[] in;
	delete[] out;
	delete[] inserted;
}

bool VF3StateSuper::NextPair(int *pn1, int *pn2, int prev_n1, int prev_n2)
{
	int curr_n1;
	int pred_pair; //Node mapped with the predecessor
	int pred_set_size = 0;
	int c = 0;

	//core_len indica la profondondita' della ricerca
	curr_n1 = order[core_len];
	c = g1->nodeLabels[curr_n1];

	if (predecessors[curr_n1] != -1)
	{
		if (prev_n2 == -1)
			last_candidate_index = 0;
		else {
			last_candidate_index++; //Next Element
		}

		pred_pair = core_1[predecessors[curr_n1]];
		bool updated = false;
		switch (dir[curr_n1])
		{
		case NODE_DIR_IN:
			pred_set_size = g2->invec[pred_pair].size();// g2->InEdgeCount(pred_pair);			
			while (last_candidate_index < pred_set_size)
			{
				prev_n2 = (*g2->invec)[pred_pair][last_candidate_index];
				if ((*commNodeLabels)[prev_n2][c] != 1)
				{
					last_candidate_index++;
					continue;
				}

				bool takeover = true;
				for (const auto& v : gm->IETreeS[curr_n1])
				{
					if (core_1[v] != -1 && core_1[v] < prev_n2)
					{
						takeover = false;
						break;
					}
				}
				if (!takeover)
				{
					return false;
				}

				if (updated)
					break;

				int maxlevel = -1;
				for (const auto& v : gm->IETreeL[curr_n1])
				{
					if (core_1[v] != -1 && core_1[v] > prev_n2)
					{
						takeover = false;
						maxlevel = max(maxlevel, core_1[v]);
						//break;
					}
				}
				if (takeover)
				{
					break;
				}
				else
				{
					updated = true;
					vector<int>* b = &(*g2->invec)[pred_pair];
					last_candidate_index = lower_bound(b->begin() + last_candidate_index, b->end(), maxlevel) - b->begin();
					continue;
				}		
			}

			break;

		case NODE_DIR_OUT:
			pred_set_size = (*g2->outedges)[pred_pair].size();

			while (last_candidate_index < pred_set_size)
			{
				prev_n2 = (*g2->outvec)[pred_pair][last_candidate_index];
				if ((*commNodeLabels)[prev_n2][c] != 1)
				{
					last_candidate_index++;
					continue;
				}

				bool takeover = true;
				for (const auto& v : gm->IETreeS[curr_n1])
				{
					if (core_1[v] != -1 && core_1[v] < prev_n2)
					{
						takeover = false;
						break;
					}
				}
				if (!takeover)
				{
					return false;
				}

				if (updated)
					break;

				int maxlevel = -1;
				for (const auto& v : gm->IETreeL[curr_n1])
				{
					if (core_1[v] != -1 && core_1[v] > prev_n2)
					{
						takeover = false;
						maxlevel = max(maxlevel, core_1[v]);
						//break;
					}
				}
				if (takeover)
				{
					break;
				}
				else
				{
					updated = true;
					vector<int>* b = &(*g2->outvec)[pred_pair];
					last_candidate_index = lower_bound(b->begin() + last_candidate_index, b->end(), maxlevel) - b->begin();
					continue;
				}
			}

			break;
		}

		if (last_candidate_index >= pred_set_size)
			return false;
	}
	else
	{
		//for nodes without any parent, prev_n2 is the indexing, else, prev_n2 is 
		//Recupero il nodo dell'esterno
		if (prev_n2 == -1)
			last_candidate_index = 0;
		else {
			last_candidate_index++; //Next Element
		}
		//else
		//	prev_n2++;

		bool updated = false;
		while (last_candidate_index < n2)
		{
			prev_n2 = (*g2->nodes)[last_candidate_index];

			if ((*commNodeLabels)[prev_n2][c] != 1)
			{
				++last_candidate_index;
				continue;
			}
			
			bool takeover = true;
			for (const auto& v : gm->IETreeS[curr_n1])
			{
				if (core_1[v] != -1 && core_1[v] < prev_n2)
				{
					takeover = false;
					break;
				}
			}
			if (!takeover)
			{
				return false;
			}

			if (updated)
				break;

			int maxlevel = -1;
			for (const auto& v : gm->IETreeL[curr_n1])
			{
				if (core_1[v] != -1 && core_1[v] > prev_n2)
				{
					takeover = false;
					maxlevel = max(maxlevel, core_1[v]);
					//break;
				}
			}
			if (takeover)
			{
				break;
			}
			else
			{
				updated = true;
				last_candidate_index = lower_bound(g2->nodes->begin() + last_candidate_index, g2->nodes->end(), maxlevel) - g2->nodes->begin();
				continue;
			}
		}

		if (last_candidate_index >= n2)
			return false;
	}
	//std::cout<<curr_n1 << " " << prev_n2 << " \n";

	if (prev_n2 <= n2) {
		*pn1 = curr_n1;
		*pn2 = prev_n2;
		//std::cout<<"\nNP END: " <<curr_n1<<" " << prev_n2 << "\n" ;
		return true;
	}

	return false;
}


/*---------------------------------------------------------------
* bool VF3State::IsFeasiblePair(node1, node2)
* Returns true if (node1, node2) can be added to the state
* NOTE:
*   The attribute compatibility check (methods CompatibleNode
*   and CompatibleEdge of ARGraph) is always performed
*   applying the method to g1, and passing the attribute of
*   g1 as first argument, and the attribute of g2 as second
*   argument. This may be important if the compatibility
*   criterion is not symmetric.
--------------------------------------------------------------*/
bool VF3StateSuper::IsFeasiblePair(int node1, int node2)
{
	//std::cout << "\nIF: " << node1 << " " << node2;
	//print_core(core_1, core_2, core_len);
	assert(node1 <= n1);
	assert(node2 <= n2);
	assert(core_1[node1] == -1);
	//assert(core_2[node2] == -1);

	//if (!nf(g1->GetNodeAttr(node1), g2->GetNodeAttr(node2)))
	//	return false;
	//int n1outsize = (*g1->outedges)[node1].size();
	//int n1insize = (*g1->inedges)[node1].size();
	//if (n1insize > g2->inNetWorkSet[node2].size()
	//	|| n1outsize > g2->netWorkSet[node2].size())
	//	return false;

	int i, other1, other2, c_other;
	//Edge1 eattr1;
	//Edge2 eattr2;
	int termout2 = 0, termin2 = 0, new2 = 0;
	memset(termin2_c, 0, classes_count * sizeof(int));
	memset(termout2_c, 0, classes_count * sizeof(int));
	memset(new2_c, 0, classes_count * sizeof(int));

	// Check the 'out' edges of node1
	//for (i = 0; i< n1insize; i++)
	//{
	for (const auto& other1 : (*g1->outedges)[node1])
	{
		//other1 = g1->GetOutEdge(node1, i, eattr1);
		c_other = g1->nodeLabels[other1];
		if (core_1[other1] != -1)
		{
			other2 = core_1[other1];
			if (!g2->HasEdge(node2, other2))//, eattr2) ||
											//!ef(eattr1, eattr2))
				return false;
		}
	}

	// Check the 'in' edges of node1
	//for (i = 0; i<g1->InEdgeCount(node1); i++)
	for (const auto& other1 : (*g1->inedges)[node1])
	{
		//other1 = g1->GetInEdge(node1, i, eattr1);
		c_other = g1->nodeLabels[other1];
		if (core_1[other1] != -1)
		{
			other2 = core_1[other1];
			if (!g2->HasEdge(other2, node2))//, eattr2) ||
											//!ef(eattr1, eattr2))
				return false;
		}
	}


	// Check the 'out' edges of node2
	//for (i = 0; i<g2->OutEdgeCount(node2); i++)
	for (const auto& other2 : (*g2->outedges)[node2])
	{
		//other2 = g2->GetOutEdge(node2, i);
		//c_other = (*g2->nodeLabels)[other2];
		if (core_2[other2] != -1)
		{
			//other1 = core_2[other2];
			//if (!g1->HasEdge(node1, other1))
			//	return false;
		}
		else
		{
			if (in_2[other2]) {
				termin2++;
				//termin1_c[c_other]++;
			}
			if (out_2[other2]) {
				termout2++;
				//termout2_c[c_other]++;
			}
			if (!in_2[other2] && !out_2[other2]) {
				new2++;
				//new2_c[c_other]++;
			}
			for (int c = 0; c < (*commNodeLabels)[other2].size(); ++c)
			{
				if ((*commNodeLabels)[other2][c] == 1)
				{
					if (in_2[other2])
						termin2_c[c]++;
					if (out_2[other2])
						termout2_c[c]++;
					if (!in_2[other2] && !out_2[other2])
						new2_c[c]++;
				}
			}
		}
	}

	// Check the 'in' edges of node2
	//for (i = 0; i<g2->InEdgeCount(node2); i++)
	for (const auto& other2 : (*g2->inedges)[node2])
	{
		//other2 = g2->GetInEdge(node2, i);
		//c_other = (*g2->nodeLabels)[other2];
		if (core_2[other2] != -1)
		{
			//other1 = core_2[other2];
			//if (!g1->HasEdge(other1, node1))
			//	return false;
		}
		else
		{
			if (in_2[other2]) {
				termin2++;
				//termin2_c[c_other]++;
			}
			if (out_2[other2]) {
				termout2++;
				//termout2_c[c_other]++;
			}
			if (!in_2[other2] && !out_2[other2]) {
				new2++;
				//new2_c[c_other]++;
			}
			for (int c = 0; c < (*commNodeLabels)[other2].size(); ++c)
			{
				if ((*commNodeLabels)[other2][c] == 1)
				{
					if (in_2[other2])
						termin2_c[c]++;
					if (out_2[other2])
						termout2_c[c]++;
					if (!in_2[other2] && !out_2[other2])
						new2_c[c]++;
				}
			}
		}
	}

	//Look-ahead check
	if ((termin1[core_len] != 0 && termin2 == 0)
		|| (termout1[core_len] != 0 && termout2 == 0))
		return false;
	else {
		for (i = 0; i < classes_count; i++) {
			if ((termin1_c[core_len][i] != 0 && termin2_c[i] == 0) 
				|| (termout1_c[core_len][i] != 0 && termout2_c[i] == 0)) {
				return false;
			}
		}
	}

	if (new1[core_len] + termin1[core_len] + termout1[core_len] != 0
		&& new2 + termin2 + termout2 == 0)
		return false;
	else
	{
		for (i = 0; i < classes_count; i++) {
			if (new1_c[core_len][i] + termin1_c[core_len][i] + termout1_c[core_len][i] != 0
		&& new2_c[i] + termin2_c[i] + termout2_c[i] == 0)
				return false;
		}
	}

	//std::cout << "\nIs Feasible: " << node1 << " " << node2;
	return true;

}



/*--------------------------------------------------------------
* void VF3State::AddPair(node1, node2)
* Adds a pair to the Core set of the state.
* Precondition: the pair must be feasible
-------------------------------------------------------------*/
void VF3StateSuper::AddPair(int node1, int node2)
{

	/*std::cout<<"\nAP:";
	print_core(core_1,core_2,n1);
	std::cout<<" <- "<< node1 <<":"<< node2;*/

	assert(node1 <= n1);
	assert(node2 <= n2);
	assert(core_len<n1);
	assert(core_len<n2);
	//assert(g1->nodeLabels[node1] == (*g2->nodeLabels)[node2]);

	//Updating the core lenght
	core_len++;
	added_node1 = node1;
	int node_c = g1->nodeLabels[node1];
	core_len_c[node_c]++;

	//Checking if node2 is not in T2_in
	if (!in_2[node2])
	{
		in_2[node2] = core_len;
		//in2_set[node_c].push_back(node2);
		t2in_len++;
		t2in_len_c[node_c]++;
		if (out_2[node2]) {
			t2both_len++;
			t2both_len_c[node_c]++;
		}
	}

	//Checking if node2 is not in T2_in
	if (!out_2[node2])
	{
		out_2[node2] = core_len;
		//out2_set[node_c].push_back(node2);
		t2out_len++;
		t2out_len_c[node_c]++;
		if (in_2[node2]) {
			t2both_len++;
			t2both_len_c[node_c]++;
		}
	}

	//Inserting nodes into the core set
	core_1[node1] = node2;
	core_2[node2] = node1;

	//Evaluation of the neighborhood
	int i, other, other_c;
	other_c = -1;

	//for (i = 0; i<g2->InEdgeCount(node2); i++)
	//{
	for (const auto& other : (*g2->inedges)[node2])
	{
		//other = g2->GetInEdge(node2, i);
		if (!in_2[other])
		{
			//other_c = (*g2->nodeLabels)[other];
			in_2[other] = core_len;
			if (out_2[other]) {
				t2both_len++;
			}
			//in2_set[other_c].push_back(other);
			t2in_len++;
			for (int c = 0; c < (*commNodeLabels)[other].size(); ++c)
			{
				if ((*commNodeLabels)[other][c] == 1)
				{
					t2in_len_c[c]++;
					if (out_2[other]) {
						t2both_len_c[c]++;
					}
				}
			}			
		}
	}

	//for (i = 0; i<g2->OutEdgeCount(node2); i++)
	for (const auto& other : (*g2->outedges)[node2])
	{
		//other = g2->GetOutEdge(node2, i);
		if (!out_2[other])
		{
			//other_c = (*g2->nodeLabels)[other];
			out_2[other] = core_len;
			if (in_2[other]) {
				t2both_len++;
			}
			//out2_set[other_c].push_back(other);
			t2out_len++;
			for (int c = 0; c < (*commNodeLabels)[other].size(); ++c)
			{
				if ((*commNodeLabels)[other][c] == 1)
				{
					t2out_len_c[c]++;
					if (in_2[other]) {
						t2both_len_c[c]++;
					}
				}
			}		
		}
	}

}



/*--------------------------------------------------------------
* void VF3State::GetCoreSet(c1, c2)
* Reads the core set of the state into the arrays c1 and c2.
* The i-th pair of the mapping is (c1[i], c2[i])
--------------------------------------------------------------*/
void VF3StateSuper::GetCoreSetSuper()
{
	unordered_map<int, vector<int>> supermatch;
	int i, j;
	for (i = 1, j = 1; i <= n1; i++)
	{
		if (core_1[i] != -1)
		{
			supermatch[core_1[i]].push_back(i);
			//gm->logger << i << " " << core_1[i] << endl;
		}
	}
	//gm->logger << endl;

	//return;
	rematch_vf3(supermatch, core_1, *communityGraphs, *g1);
	
	//gm->logger << endl;
}

/*----------------------------------------------------------------
* Undoes the changes to the shared vectors made by the
* current state. Assumes that at most one AddPair has been
* performed.
----------------------------------------------------------------*/
void VF3StateSuper::BackTrack()
{

	/*std::cout<<"\nBT:";
	print_core(core_1,core_2,n1);
	std::cout<<" -> "<< added_node1 <<":"<< core_1[added_node1];*/

	assert(core_len - orig_core_len <= 1);
	assert(added_node1 != -1);

	int other_c = 0;
	int node_c = g1->nodeLabels[added_node1];

	if (orig_core_len < core_len)
	{
		int i, node2;
		node2 = core_1[added_node1];

		if (in_2[node2] == core_len) {
			in_2[node2] = 0;
			//in2_set[node_c].erase(node2);
			t2in_len_c[node_c]--;
			if (out_2[node2])
				t2both_len_c[node_c]--;
		}

		if (out_2[node2] == core_len) {
			out_2[node2] = 0;
			//out2_set[node_c].erase(node2);
			t2out_len_c[node_c]--;
			if (in_2[node2])
				t2both_len_c[node_c]--;

		}

		//Backtraking neightborhood
		//for (i = 0; i<g2->InEdgeCount(node2); i++)
		for (const auto& other : (*g2->inedges)[node2])
		{
			//int other = g2->GetInEdge(node2, i);
			//other_c = (*g2->nodeLabels)[other];
			if (in_2[other] == core_len) {
				in_2[other] = 0;
				//in2_set[other_c].erase(other);
				for (int c = 0; c < (*commNodeLabels)[other].size(); ++c)
				{
					if ((*commNodeLabels)[other][c] == 1)
					{
						t2in_len_c[c] --;
						if (out_2[other])
							t2both_len_c[c]--;
					}
				}	
			}
		}

		//for (i = 0; i<g2->OutEdgeCount(node2); i++)
		for (const auto& other : (*g2->outedges)[node2])
		{
			//int other = g2->GetOutEdge(node2, i);
			//other_c = (*g2->nodeLabels)[other];
			if (out_2[other] == core_len) {
				out_2[other] = 0;
				//out2_set[other_c].erase(other);
				for (int c = 0; c < (*commNodeLabels)[other].size(); ++c)
				{
					if ((*commNodeLabels)[other][c] == 1)
					{
						t2out_len_c[c] --;
						if (in_2[other])
							t2both_len_c[c]--;
					}
				}		
			}
		}

		core_1[added_node1] = -1;
		core_2[node2] = -1;

		core_len = orig_core_len;
		core_len_c[node_c]--;
		added_node1 = -1;
	}
}

bool VF3StateSuper::IsDead() {
	if ((t1both_len[core_len] != 0 && t2both_len == 0)
		|| (t1out_len[core_len] != 0 && t2out_len == 0)
		|| (t1in_len[core_len] != 0 && t2in_len == 0) )
	{
		return true;
	}

	for (int c = 0; c < classes_count; c++) {
		if ((t1both_len_c[core_len][c] != 0 && t2both_len_c[c] == 0) 
			|| (t1out_len_c[core_len][c] != 0 && t2out_len_c[c] == 0)
			|| (t1in_len_c[core_len][c] != 0 && t2in_len_c[c] == 0)) 
		{
			return true;
		}
	}

	return false;
}

void VF3StateSuper::rematch_vf3(unordered_map<int, vector<int>>& supermatch, int* supermatchmap
	, vector<TempGraph*>& communityGraphs, TempGraph& patternGraph)
{
	bool cut1 = false;
	bool cut2 = true;//true;
	bool cut3 = true;
	//cout << "info" << endl;
	bool isgo = true;

	for (auto& n : supermatch)
	{
		if (n.second.size() > data->communityNodes[n.first].size())
		{
			isgo = false;
			break;
		}

		//sort(n.second.begin(), n.second.end());
	}

	if (!isgo)
	{
		return; //continue;
	}

	if (supermatch.size() == 1)
	{
		//cout << supermatch.begin()->first << endl;
		if (recin->g2 == NULL)
		{
			//recin = new VF3StateIn(&patternGraph, NULL, gm, data->labelnum);
			recin->g2 = communityGraphs[supermatch.begin()->first];
			recin->initG2();
		}
		else
		{
			recin->g2 = communityGraphs[supermatch.begin()->first];
			recin->initG2();
			recin->initG1();
		}
		
		int count = recin->match();

		//rectm->vvans = &tans[0];
		//int count = rectm->TurboISO(rectm->q, rectm->g, candup, supermatch.begin()->first);

		gm->internum++;
		//#pragma omp critical
		{
			gm->ansnum += count;
		}
		return;//continue;
	}
	//return;

	gm->uselessUntrivial++;

	//int id = omp_get_thread_num();
	vector<map<int, int>> newallmaps;
	bool smallestPattern = false;

	//supermatch = s;

	bool canMatch = true;

	bool canfind = true;
	vector<vector<int>*> boundary;
	vector<vector<int>*> pointers;

	
	gm->uselessCut2++;

	vector<int> allmaps;
	if (cut3)
	{
		/*for (const auto& n : supermatchmap)
		{
		mystr += n.second;
		}*/

		//vector<map<int, int>> allmaps;
		unordered_set<string> record;

		if (!(gm->getCompleteMatch(supermatchmap, allmaps, record)))//!(gm->getAllInPatternCompleteMatch(supermatch, supermatchmap, mystr, supermatch.begin(), newallmaps, cMap, usednodes)))
		{
			for (int e = 0; e < pointers.size(); ++e)
			{
				delete pointers[e];
			}
			//cout << "catch!" << endl;
			//for (auto& n : supermatchmap)
			//{
			//	gm->logger << n.first << " " << n.second << endl;
			//}
			//gm->logger << endl;
			return;// continue;
		}
	}

	//unordered_map<int, unordered_map<int, unordered_map<int, int>>> oomessage;//, oimessage, iomessage;
	//storage->tools->getTwoHopPatternPairs(&patternGraph, supermatchmap, oomessage, oomessage, oomessage);//oimessage, iomessage);

	//TempGraph t(*q->nodes, &nodeAttributes, &edgeAttributes, *q->outedges, *q->outedges);
	bool candup = false;
	if (recbound == NULL)
	{
		recbound = new VF3StateBound(&patternGraph, originalgraph, gm, data->labelnum);
		recbound->communityGraphs = this->communityGraphs;
		recbound->data = data;
	}
	//TurboMatch tm(-1, &boundary, NULL, NULL, NULL, storage, &patternGraph, originalgraph);
	//tm.storeType = 0;
	//tm.communityGraphs = this->communityGraphs;
	recbound->init();
	if (cut2)
	{
		recbound->nodeArea = &boundary;
	}
	else
	{
		recbound->nodeArea = NULL;
	}
	//vector<vector<int>> finds;
	//recbound->vvans = &finds;
	recbound->distributeplan = supermatchmap;
	//boundtm->newallmaps = &newallmaps;

	//cout << supermatchmap[1] << " "<< supermatchmap[2] << " " <<supermatchmap[3] << " " << supermatchmap[4] <<endl;
	//if (supermatchmap[1] == 9 && supermatchmap[2] == 9 && supermatchmap[3] == 9 && supermatchmap[4] == 10)
	//	int a = 0;
	int count = recbound->match();
	gm->internum++;
	//cout << count << endl;
	if (count == 0)
	{
		gm->uselessCS++;
		//for (auto& n : supermatchmap)
		//{
		//	gm->logger << n.first << " " << n.second << endl;
		//}
		//gm->logger << endl;

		for (auto& n : supermatch)
		{
			if (n.second.size() >= 2)
			{
				gm->uselessDouble++;
				break;
			}
		}
	}
	else
	{
		gm->usefulCS++;
	}

	for (int e = 0; e < pointers.size(); ++e)
	{
		delete pointers[e];
	}

	if (cut3)
	{
		//#pragma omp critical
		{
			gm->ansnum += count * allmaps.size();
		}
		/*for (int f = 0; f < finds.size(); f++)
		{
			for (int i = 0; i < allmaps.size(); ++i)
			{
				vector<int> newmap(finds[f].size(), -1);
				for (int j = 1; j < gm->schemes[allmaps[i]].size(); ++j)
				{
					newmap[j - 1] = finds[f][gm->schemes[allmaps[i]][j] - 1];
				}
				for (int k = 0; k < newmap.size(); k++)
				{
					gm->logger << k + 1 << " " << newmap[k] << endl;
				}
				gm->logger << endl;
			}
		}
		/*vector<map<int, int>>::iterator sit = newallmaps.begin();
		while (sit != newallmaps.end())
		{
		map<int, int> m = *sit;
		vector<int> newmap(finds[f].size(), -1);
		for (int i = 0; i < finds[f].size(); i++)
		{
		if (finds[f][i] != -1)
		{
		newmap[m[i + 1] - 1] = finds[f][i];
		}
		}
		//int id = 0;
		//tans[id].push_back(newmap);
		for (int k = 0; k < newmap.size(); k++)
		{
		gm->logger << k + 1 << " " << newmap[k] << endl;
		}
		gm->logger << endl;

		sit++;
		}*/
		//}
	}
	else
	{
		//#pragma omp critical
		//{
		gm->ansnum += count;
		//}
		//for (int f = 0; f < finds.size(); f++)
		//{
		//tans[0].push_back(finds[f]);
		//}
	}

	//for (const auto& m : dels)
	//{
	//	delete maps[m];
	//}
	//maps.clear();
	//currentMap.clear();
	//commvec.clear();
	//}
}

bool VF3StateSuper::match_super(VF3StateSuper &s, int *pn)
{
	if (s.IsGoal())
	{
		//++*pn;
		//int n = s.CoreLen();
		s.GetCoreSetSuper();
		return false;
	}

	if (s.IsDead())
		return false;

	int n1 = -1, n2 = -1;

	while (s.NextPair(&n1, &n2, n1, n2))
	{
		if (s.IsFeasiblePair(n1, n2))
		{
			VF3StateSuper s1(s);
			s1.AddPair(n1, n2);
			if (match_super(s1, pn))
			{
				return true;
			}
		}
	}
	return false;
}

int VF3StateSuper::match()
{
	initIETree();

	VF3NodeSorter sorter(g2);
	vector<int> sorted = sorter.SortNodes(g1);
	this->order = sorted.data();

	ComputeFirstGraphTraversing();
	int n = 0;
	match_super(*this, &n);

	return 0;
}

void VF3StateSuper::initIETree()
{
	gm->IETreeL = vector<vector<int>>(g1->nodenum + 1);
	gm->IETreeS = vector<vector<int>>(g1->nodenum + 1);
	vector<unordered_set<int>> check(g1->nodenum + 1);
	int index = 0;
	for (int i = 0; i < gm->schemes.size(); ++i)
	{
		for (int j = 1; j <= g1->nodenum; ++j)
		{
			if (gm->schemes[i][j] != j)
			{
				if (check[j].find(gm->schemes[i][j]) == check[j].end())
				{
					gm->IETreeS[j].push_back(gm->schemes[i][j]);
					gm->IETreeL[gm->schemes[i][j]].push_back(j);
				}
				break;
			}
		}
	}
}