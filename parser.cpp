#if defined(__INTELLISENSE__)
#pragma once
#include "build.cpp"
#include <string>
#include <functional>
#include <iterator>
#include <optional>
#include <iostream>
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"
#else
export module parser;
import build;
import <string>;
import <functional>;
import <iterator>;
import <optional>;
import <iostream>;
import "llvm/IR/LLVMContext.h";
import "llvm/IR/Module.h";
import "llvm/IR/Function.h";
import "llvm/IR/BasicBlock.h";
import "llvm/IR/IRBuilder.h";
import "llvm/IR/Verifier.h";
import "llvm/ExecutionEngine/ExecutionEngine.h";
import "llvm/ExecutionEngine/GenericValue.h";
import "llvm/Support/TargetSelect.h";
#endif
namespace parser {
	export class Node {
	public:
		std::string value;

		std::vector<std::unique_ptr<Node> > branch;
		template <class T>
		bool equal() {
			return dynamic_cast<T*>(this) != nullptr;
		}
		virtual llvm::Value* codegen(build::Builder&) {
			return nullptr;
		}
	};
	export class BNF {
	private:
		using Iter = decltype(Node::branch)::iterator&;
		std::function<std::optional<std::unique_ptr<Node> >(Iter)> parser;
	public:
		BNF(decltype(parser) parser) :parser(parser) {}
		BNF() {}
		template <class T>  requires std::derived_from<T, Node>
		auto set() {
			parser = [](Iter iter)->decltype(parser)::result_type {
				auto node = std::make_unique<Node>();
				node.get()->value = iter->get()->value;
				if (!iter->get()->equal<T>())return std::nullopt;
				++iter;
				return std::move(node);
			};
			return *this;
		}
		BNF(decltype(Node::value) str) :parser(
			[str = std::move(str)](Iter iter) ->decltype(parser)::result_type{
			auto node = std::make_unique<Node>();
			node.get()->value = iter->get()->value;
			if (iter->get()->value != str)return std::nullopt;
			++iter;
			return std::move(node);
		}
		) {}
		auto operator()(decltype(Node::branch)& data) {
			data.emplace_back(std::make_unique<Node>());
			auto iter = data.begin();
			return parser(iter);
		}
		template <class T>  requires std::derived_from<T, Node>
		auto regist() {//regist
			return BNF([parser = this->parser](Iter data)->decltype(parser)::result_type {
				const auto temp = parser(data);
				if (!temp)return std::nullopt;
				auto node = std::make_unique<T>();
				node.get()->value = temp.value().get()->value;
				node.get()->branch = std::move(temp.value().get()->branch);
				return std::move(node);
			});
		}
		auto operator~() {//push node
			return BNF([parser = this->parser](Iter iter) ->decltype(parser)::result_type{
				auto node = std::make_unique<Node>();
				auto child = parser(iter);
				if (!child)return std::nullopt;
				node.get()->branch.emplace_back(std::move(child.value()));
				return std::move(node);
			});
		}
		auto operator|(BNF bnf) {//or
			return BNF([selfParser = this->parser, parser = bnf.parser](Iter data)->decltype(parser)::result_type {
				auto node = selfParser(data);
				if (node)return std::move(node);
				return std::move(parser(data));
			});
		}
		auto operator&() {//reference
			return BNF([this](Iter iter) ->decltype(parser)::result_type{
				return std::move(this->parser(iter));
			});
		}
		auto operator+(BNF bnf) {//succession
			return BNF([selfParser = this->parser, parser = std::move(bnf.parser)](Iter data)->decltype(parser)::result_type {
				const auto temp = data;
				auto node = selfParser(data);
				if (!node) {
					data = temp;
					return std::nullopt;
				}
				auto branch = std::move(node.value().get()->branch);
				node = parser(data);
				if (!node) {
					data = temp;
					return std::nullopt;
				}
				node.value().get()->branch.insert(node.value().get()->branch.begin(), std::make_move_iterator(branch.begin()), std::make_move_iterator(branch.end()));
				return std::move(node);
			});
		}
		//auto operator-(BNF bnf) {//expect
		//	return BNF([selfParser = this->parser, parser = bnf.parser](Iter iter)->decltype(parser)::result_type {
		//		auto node = selfParser(iter);
		//		if (!node || !parser(iter))return std::nullopt;
		//		return std::move(node);
		//	});
		//}
		auto operator,(BNF bnf) {//link string
			return BNF([selfParser = this->parser, parser = std::move(bnf.parser)](Iter data) ->decltype(parser)::result_type{
				const auto temp = data;
				auto self = selfParser(data);
				if (!self) {
					data = temp;
					return std::nullopt;
				}
				const auto  node = parser(data);
				if (!node) {
					data = temp;
					return std::nullopt;
				}
				self.value().get()->value += node.value().get()->value;
				return std::move(self);
			});
		}
	};
}