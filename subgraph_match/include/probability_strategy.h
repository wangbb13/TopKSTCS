#pragma once
#ifndef PROBABILITY_STRATEGY_HPP
#define PROBABILITY_STRATEGY_HPP

#include "Graph.h"

class NodeProbabilityStrategy {
protected:
	double* degree; //Array of degree probability
	double* out_deg; //Array of "out" degree probability
	double* in_deg; //Array of "in" degree probability
	int degree_size;
	int out_deg_size;
	int in_deg_size;

	map<int, double> labels; //Map of labels probability

	virtual void evaluateProbabilities(Graph* g2);
	virtual void evaluateProbabilities(TempGraph* g2);

public:
	NodeProbabilityStrategy(Graph* g2) {
		evaluateProbabilities(g2);
	}
	NodeProbabilityStrategy(TempGraph* g2) {
		evaluateProbabilities(g2);
	}

	~NodeProbabilityStrategy() {
		delete[] out_deg;
		delete[] in_deg;
		delete[] degree;
	}

	virtual double getProbability(TempGraph *g1, int id) = 0;
};

class SubIsoNodeProbability : public NodeProbabilityStrategy {
public:
	SubIsoNodeProbability(Graph* source) :NodeProbabilityStrategy(source) {}
	SubIsoNodeProbability(TempGraph* source) :NodeProbabilityStrategy(source) {}
	double getProbability(TempGraph* g, int id);
	virtual ~SubIsoNodeProbability() {}
};

#endif
