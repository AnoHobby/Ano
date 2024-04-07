#if defined(__INTELLISENSE__)
#pragma once
#include <unordered_map>
#include <memory>
#include <optional>
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
export module build;
import <unordered_map>;
import <memory>;
import <optional>;
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
#include "share.cpp"
namespace build {
	export class Scope_Interface {
	private:
	public:
		virtual void scope_nest() = 0;
		virtual void scope_break() = 0;
	};
	template <typename T>
	class Scope:public Scope_Interface{
	protected:
			std::vector<std::unordered_map<std::string, T > > target;
	public:
		void scope_nest()override {
			target.emplace_back();
		}
		void scope_break()override {
			target.pop_back();
		}

		template <class keyT, class valueT>
		auto insert_or_assign(keyT&& key, valueT&& value) noexcept(false/*scope_nest<scopebreak*/) {
			target.back().insert_or_assign(std::forward<keyT>(key), std::forward<valueT>(value));
		}
		std::optional<typename decltype(target)::value_type::mapped_type> serch(const typename decltype(target)::value_type::key_type name) {
			for (auto& scope : share::Reverse(target)) {
				if (scope.contains(name))return scope[name];
			}
			return std::nullopt;
		}
		std::optional<std::size_t> serch_nest(const typename decltype(target)::value_type::key_type name) {
			for (auto nest=target.size(); auto & scope : share::Reverse(target)) {
				if (scope.contains(name))return nest;
				++nest;
			}
			return std::nullopt;
		}
		auto get_nest() {
			return target.size();
		}
	};
	//export class Variables :public  Scope<llvm::Value*>{
	//private:
	//public:

	//	Variables() {

	//	}
	//};
	export class PHI:public Scope<std::pair<llvm::BasicBlock*,std::vector<std::pair<llvm::Value*, llvm::BasicBlock*> > > >{
	private:
	public:
		template <class keyT>
		auto init(keyT&& key, llvm::BasicBlock* value) noexcept(false/*scope_nest<scopebreak*/) {
			Scope::insert_or_assign(std::forward<keyT>(key), std::make_pair(value,std::vector<std::pair<llvm::Value*, llvm::BasicBlock*> >{}));
		}
		template <class keyT>
		auto push(keyT&& key, llvm::Value* first,llvm::BasicBlock* second) noexcept(false/*scope_nest<scopebreak*/) {
			if (auto nodes = serch(key);nodes) {//超絶非効率
				nodes.value().second.emplace_back(std::make_pair(first, second));
				Scope::insert_or_assign(std::forward<keyT>(key), nodes.value());
			}
		}
		auto create(llvm::IRBuilder<>& builder, const std::string key) {
			const auto nodes = serch(key).value().second;
			llvm::PHINode* phiNode = builder.CreatePHI(nodes.front().first->getType(), nodes.size(), "");//型チェック必要あればする
			for (const auto& [value, block] : nodes) {
				phiNode->addIncoming(value, block);
			}
			//生成したphiは削除する
			return phiNode;
		}
	};
	export class Builder {
	private:
		llvm::LLVMContext context;
		std::unique_ptr<llvm::Module> mainModule;
		llvm::IRBuilder<> builder;
		Scope<llvm::Value*> variables;
		PHI phi;
	public:
		Builder() :
			mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
			builder(context)
		{
			context.setOpaquePointers(false);
		}
		auto& getBuilder() {
			return builder;
		}
		auto& getModule() {
			return mainModule;
		}
		auto& getVariables() {
			return variables;
		}
		auto& getPhi() {
			return phi;
		}
		auto scope_nest() {
			variables.scope_nest();
			phi.scope_nest();
		}
		auto scope_break() {
			variables.scope_break();//todo:Interfaceとしてfor文回す
			phi.scope_break();
		}
		std::optional<llvm::Type*> string_to_type(const std::string type) {
			switch (type.front()) {
			case 'v':
				return builder.getVoidTy();
				break;
			case 'd':
				return builder.getDoubleTy();
				break;
			case 'f':
				return builder.getFloatTy();
				break;
			case 'u':
			case 'i':
				return builder.getIntNTy(
					std::stoi(type.substr(1))
				);
				break;

			}
			return std::nullopt;
		}
	};
}