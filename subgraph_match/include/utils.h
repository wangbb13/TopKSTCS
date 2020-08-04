#pragma once
#include <sstream>
#include <string>

template <typename DataType>
std::string __to_string(DataType val) {
	std::string str;
	std::stringstream ss;
	ss << val;
	ss >> str;
	return str;
}