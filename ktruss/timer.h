//
// Created by Luo on 2020/3/3.
//

#ifndef SOURCE_TIMER_H
#define SOURCE_TIMER_H

#include <iostream>
#include "time.h"
#include "sys/time.h"
#include "stdio.h"
#include "stdlib.h"
#include "math.h"
#include "string.h"
#include <fstream>

using namespace std;

class CUtility {
public:
    CUtility() {
    }

    ~CUtility() {
    }

public:
    inline void start();

    inline double end(string desc);

    inline void setFILE(FILE* fp);
private:
    timeval startTime;
    timeval endTime;

    FILE* fp;
};

void CUtility::start() {
    gettimeofday(&startTime, NULL);
}

double CUtility::end(string desc) {
    gettimeofday(&endTime, NULL);
    double duration = (double) (endTime.tv_sec - startTime.tv_sec) * 1000 +
                      (double) (endTime.tv_usec - startTime.tv_usec) / 1000;

    if (fp == NULL) {
        fprintf(stdin, "In %s, #Time consumption: %.3f ms (%.2f s)\n", desc.c_str(), duration, duration / 1000);
    } else {
        fprintf(fp, "In %s, #Time consumption: %.3f ms (%.2f s)\n", desc.c_str(), duration, duration / 1000);
    }

    return duration;
}

void CUtility::setFILE(FILE *fp) {
    this->fp = fp;
}

#endif //SOURCE_TIMER_H
