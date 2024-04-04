#if defined(__INTELLISENSE__)
#pragma once
#include <string>
#include <fstream>
#include <iterator>
#include <optional>
#else
export module file;
import <string>;
import <fstream>;
import <iterator>;
import <optional>;
#endif
namespace file {
	export class File {
	private:
		const std::string name;
	public:
		File(decltype(name) name) :name(name) {

		}
		std::optional<std::string> read() {
			std::fstream file(name.c_str());
			if (!file)return std::nullopt;
			return std::move(std::string(std::istreambuf_iterator<decltype(name)::value_type >(file), std::istreambuf_iterator<decltype(name)::value_type>()));
		}
		auto write(decltype(name) content) {
			std::ofstream file(name.c_str());
			if (!file)return false;
			file << std::move(content);
			return true;
		}
	};
}