#define __ALL_IMPORT__
#if defined(__INTELLISENSE__)
#pragma once
#include "file.cpp"
#include "parser.cpp"
#include <string>
#include <algorithm>
#include <functional>
#include <vector>
#include <iostream>
#include <iterator>
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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"

#else
import parser;
import file;
import <string>;
import <algorithm>;
import <functional>;
import <vector>;
import <iostream>;
import <iterator>;
import <optional>;
import "llvm/IR/LLVMContext.h";
import "llvm/IR/Module.h";
import "llvm/IR/Function.h";
import "llvm/IR/BasicBlock.h";
#if defined(__ALL_IMPORT__)
import "llvm/IR/IRBuilder.h";
#else
#include "llvm/IR/IRBuilder.h";
#endif
import "llvm/IR/Verifier.h";
import "llvm/ExecutionEngine/ExecutionEngine.h";
import "llvm/ExecutionEngine/GenericValue.h";
import "llvm/Support/TargetSelect.h";

import "llvm/IR/Instructions.h";
import "llvm/IR/Type.h";
import "llvm/Transforms/Utils/Cloning.h";
import "llvm/Transforms/Utils/ValueMapper.h";

import "llvm/Support/FileSystem.h";
import "llvm/Support/raw_ostream.h";
import "llvm/Bitcode/BitcodeWriter.h";
#endif
//todo:ano langの構文を定義するモジュールで定義
static constexpr auto avoid_duplication_with_user_definition(std::string internally_used_name) {
	return "." + std::move(internally_used_name);
}
//class Digit:public Node{};
//BNF().set<Digit>();->BNF().set<Tag<TAG::DIGIT/*enum class etc...*/> >();

template <auto T>
class Tag :public parser::Node {};
class Block :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {//return と同じ機構で作る
		enum {
			NAME,
			NAMED_BLOCK_FLAG
		};
		builder.scope_nest();
		if (NAMED_BLOCK_FLAG/*named block*/ < branch.size()) {//AST生成時点でblockとnamedblockを区別しておいた方がいいかもしれない
			builder.getPhi().init(
				branch[NAME]->value,
				llvm::BasicBlock::Create(builder.getBuilder().getContext(), branch[NAME]->value,//idea:下から一番近いところをfirstとして使う
					builder.getBuilder().GetInsertBlock()->getParent()
				)
			);
		}
		llvm::Value* result;
		for (const auto& child : branch.back()->branch) {
			result = child->codegen(builder);
		}

		if (NAMED_BLOCK_FLAG < branch.size()) {
			builder.getBuilder().SetInsertPoint(builder.getPhi().search(branch[NAME]->value).value().first);
			//builder.getBuilder().CreateBr(builder.getPhi().search(branch[NAME]->value).value().first);
			if (builder.getPhi().search(branch[NAME]->value).value().second.size())result = builder.getPhi().create(builder.getBuilder(), branch[NAME]->value);

		}

		builder.getVariables().scope_break();
		return result;
	}
};
class Reference :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getVariables().search(value).value();
	}
};

class Load :public parser::Node {
public:
	llvm::Value* codegen(build::Builder& builder)override {
		const auto value = branch.front()->codegen(builder);
		if (value->getType()->isPointerTy())
			return builder.getBuilder().CreateLoad(
				value->getType()->getNonOpaquePointerElementType(),
				value
			);
		return value;
	}
};

class Var :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			NAME,
			VALUE
		};
		builder.getVariables().insert_or_assign(branch[NAME]->value, branch[VALUE]->codegen(builder));
		//return builder.getVariables().search(branch[NAME]->value).value();
		Load loader;
		loader.branch.emplace_back(std::make_unique<Reference>());
		loader.branch.front()->value = std::move(branch[NAME]->value);
		return loader.codegen(builder);//loadが不要な場面もある
	}
};
class Mutable :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		auto* value = branch.front()->codegen(builder);
		if (value->getType()->isPointerTy())return value;
		auto* variable = builder.getBuilder().CreateAlloca(value->getType());
		builder.getBuilder().CreateStore(value, variable);
		return variable;
	}
};
class Assign :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateStore(branch.back()->codegen(builder), branch.front()->codegen(builder)/*codegen()->to_pointer*/);
	}
};

class Int :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			VALUE,
			INFO
		};
		return llvm::ConstantInt::get(
			builder.getBuilder().getContext(),
			llvm::APInt(
				std::stoi(branch[INFO]->value.substr(1)),
				std::stoi(branch[VALUE]->value),
				branch[INFO]->value.front() == 'u'
			)
		);
	}
};
template <auto F>
class Floating_Point :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return llvm::ConstantFP::get(
			(*F)(builder.getBuilder().getContext()),
			std::stod(branch.front()->value)
		);
	}
};
//todo:return {0i32;};がエラーになる
class Return :public parser::Node {
private:
public:
	static constexpr const char* ret_ident = "return";
	llvm::Value* codegen(build::Builder& builder)override {

		enum {
			NAME,
			CODE
		};
		llvm::Value* value;
		if (branch.size() == 2 && branch.front()->value == ret_ident && branch.back()->equal<Load>() && builder.getPhi().search(branch.back()->value)) {
			branch.erase(branch.begin());
		}
		if (CODE < branch.size())value = branch.back()->codegen(builder);
		else {
			builder.getBuilder().CreateBr(builder.getPhi().search(branch[NAME]->value).value().first);
			return nullptr;
		}
		if (value->getType()->isIntegerTy(0))return nullptr;
		builder.getPhi().push(branch[NAME]->value, value, builder.getBuilder().GetInsertBlock());
		builder.getBuilder().CreateBr(builder.getPhi().search(branch[NAME]->value).value().first);
		return value;
	}
};
class MyTypeMapper : public llvm::ValueMapTypeRemapper {
private:
	llvm::Type* type;
	bool changed = false;
public:
	MyTypeMapper(decltype(type) type) :type(type) {}
	llvm::Type* remapType(llvm::Type* old) override {
		if (old->isIntegerTy(0)) {
			changed = true;
			return type;
		}
		return old;
	}
	auto& is_changed()const noexcept {
		return changed;
	}
};
class Function :public parser::Node {
private:
	llvm::Type* ret_type;
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			NAME,
			ARGUMENTS,
		};
		branch[NAME]->codegen(builder);
		std::vector<llvm::Type*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = builder.getTypeAnalyzer().analyze(branch[ARGUMENTS]->branch[i]->branch.front()->value).value();
			++i;
		}
		if (builder.getTypeAnalyzer().analyze(builder.get_namespace().get_path())) {
			//argsは最後の方が効率がいいかも
			args.insert(args.begin(), builder.getTypeAnalyzer().analyze(builder.get_namespace().get_path()).value()->getPointerTo());
			branch[ARGUMENTS]->branch.emplace(branch[ARGUMENTS]->branch.begin(), std::make_unique<Node>());
			branch[ARGUMENTS]->branch.front()->branch.resize(1);//dummy
			branch[ARGUMENTS]->branch.front()->branch.emplace_back(std::make_unique<Node>());
			branch[ARGUMENTS]->branch.front()->branch.back()->value = "this";
		}

		if (!ret_type) {
			ret_type =llvm::Type::getIntNTy(builder.getBuilder().getContext(), 0);
		}
		builder.getBuilder().SetInsertPoint(
			llvm::BasicBlock::Create(builder.getBuilder().getContext(), "entry",
				llvm::Function::Create(
					llvm::FunctionType::get(ret_type,
						llvm::ArrayRef(args), false),
					llvm::Function::ExternalLinkage, avoid_duplication_with_user_definition(branch[NAME]->value), *builder.getModule())
			)
		);

		builder.scope_nest();
		builder.getPhi().init(
			Return::ret_ident,
			llvm::BasicBlock::Create(builder.getBuilder().getContext(), "return",
				builder.getBuilder().GetInsertBlock()->getParent()
			)
		);
		for (auto i = 0; auto & arg : builder.getBuilder().GetInsertBlock()->getParent()->args()) {
			if (arg.getType()->isPointerTy()) {
				builder.getVariables().insert_or_assign(
					branch[ARGUMENTS]->branch[i]->branch[1]->value,
					&arg
				);
			}
			else {
				builder.getVariables().insert_or_assign(
					branch[ARGUMENTS]->branch[i]->branch[1]->value,
					builder.getBuilder().CreateAlloca(arg.getType())
				);
				builder.getBuilder().CreateStore(&arg, builder.getVariables().search(branch[ARGUMENTS]->branch[i]->branch[1]->value).value());
			}
			++i;
		}

		branch.back()->codegen(builder);//block nodeの処理が終わるとret_identのスコープも切れるので、scope_nestをする

		builder.getBuilder().SetInsertPoint(builder.getPhi().search(Return::ret_ident).value().first);
		builder.getBuilder().CreateRet(builder.getPhi().search(
			Return::ret_ident).value().second.size() ?
			builder.getPhi().create(builder.getBuilder(), Return::ret_ident) :
			nullptr
		);
		builder.getModule()->print(llvm::outs(), nullptr);

		if (builder.getBuilder().GetInsertBlock()->getParent()->getReturnType()->isIntegerTy(0)) {
			ret_type = builder.getPhi().search(Return::ret_ident).value().second.size() ?
				builder.getPhi().search(Return::ret_ident).value().second.front().first->getType() :
				builder.getBuilder().getVoidTy();
			MyTypeMapper tm(ret_type);
			llvm::ValueToValueMapTy vmap;
			llvm::SmallVector <llvm::ReturnInst*, 0> returns;
			auto* clone = llvm::Function::Create(
				llvm::FunctionType::get(ret_type,
					llvm::ArrayRef(args), false),
				llvm::Function::ExternalLinkage, branch[NAME]->value, *builder.getModule()
			);
			for (auto iter = clone->args().begin(); const auto & arg : builder.getBuilder().GetInsertBlock()->getParent()->args()) {
				vmap[&arg] = iter;
				++iter;
			}
			vmap[builder.getBuilder().GetInsertBlock()->getParent()] = clone;
			llvm::CloneFunctionInto(
				clone,
				builder.getBuilder().GetInsertBlock()->getParent(),
				vmap,
				llvm::CloneFunctionChangeType::DifferentModule,
				returns,
				"",
				nullptr,
				&tm
			);
			builder.getModule()->getFunction(avoid_duplication_with_user_definition(branch[NAME]->value))->eraseFromParent();
			if (tm.is_changed()) {
				ret_type = builder.getPhi().search(Return::ret_ident).value().second.front().first->getType();
				builder.getVariables().scope_break();
				builder.scope_nest();
				builder.getModule()->getFunction(branch[NAME]->value)->eraseFromParent();
				//branch[RET_TYPE]->value ="i32";直接指定するとret_typeを保持しなくてよくなる
				codegen(builder);
			}
		}
		else {
			builder.getBuilder().GetInsertBlock()->getParent()->setName(branch[NAME]->value);
		}
		builder.getVariables().scope_break();
		return 	builder.getModule()->getFunction(branch[NAME]->value);
	}
};
class Call :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum {
			NAME,
			ARGUMENTS
		};
		//branch[NAME]->codegen(builder);
		std::vector<llvm::Value*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg:args) {
			arg = branch[ARGUMENTS]->branch[i]->codegen(builder);
			++i;
		}
		constexpr decltype(branch[NAME]->value) constructor = "::new";//uncool
		if (constructor.size() < branch[NAME]->value.size() && std::equal(branch[NAME]->value.end() - constructor.size(), branch[NAME]->value.end(), constructor.begin(), constructor.end())) {
			args.insert(
				args.begin(),
				builder.getBuilder().CreateAlloca(builder.getTypeAnalyzer().analyze(std::move(branch[NAME]->value.substr(0, branch[NAME]->value.size() - constructor.size()))).value())
			);
		}
		//ret_ident型を返す関数を新しく作る
		if (!builder.getModule()->getFunction(branch[NAME]->value))return builder.getBuilder().CreateCall(builder.getModule()->getFunction(avoid_duplication_with_user_definition(branch[NAME]->value)), args);;
		return builder.getBuilder().CreateCall(builder.getModule()->getFunction(branch[NAME]->value), args);

	}
};
class If :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum {
			COND,
			IF,
			ELSE,
		};
		//const auto ifblock=
		auto* ifBlock = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "if", builder.getBuilder().GetInsertBlock()->getParent()),
			* elseBlock = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "else", builder.getBuilder().GetInsertBlock()->getParent()),
			* after = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "after", builder.getBuilder().GetInsertBlock()->getParent());
		builder.getBuilder().CreateCondBr(
			branch.front()->codegen(builder),
			ifBlock,
			elseBlock
		);
		builder.getBuilder().SetInsertPoint(ifBlock);
		//if(let mut a=0i32;a<0){}のような初期化構文があればここでscope_nestするかblockNodeにlet mut a=0を持ってきて残りをIfとしてpushする
		//ifnode{if_init,cond,if,else}->blocknode{if_init,ifnode{cond,if,else} };
		branch[IF]->codegen(builder);
		builder.getBuilder().SetInsertPoint(elseBlock);
		if (ELSE < branch.size())branch[ELSE]->codegen(builder);
		auto needErase = true;
		if (elseBlock->getInstList().back().getOpcode() != llvm::Instruction::Br) {
			builder.getBuilder().CreateBr(after);
			needErase = false;
		}
		if (ELSE < branch.size() && branch[ELSE]->equal<If>()) {
			after->eraseFromParent();
			after = builder.getBuilder().GetInsertBlock();
			needErase = false;
		}
		if (ifBlock->getInstList().back().getOpcode() != llvm::Instruction::Br) {
			builder.getBuilder().SetInsertPoint(ifBlock);
			builder.getBuilder().CreateBr(after);
			needErase = false;
		}
		if (needErase) {//search_nestとget_nestで同じスコープか見てafterを作成すると良い
			after->eraseFromParent();
		}
		else builder.getBuilder().SetInsertPoint(after);


		return nullptr;//todo:値を返す
	}
};

class Extern :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum {
			NAME,
			ARGUMENTS,
		};
		std::vector<llvm::Type*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = builder.getTypeAnalyzer().analyze(branch[ARGUMENTS]->branch[i]->value).value();
			++i;
		}
		builder.getModule()->getOrInsertFunction(
			branch[NAME]->value,
			llvm::FunctionType::get(
				builder.getTypeAnalyzer().analyze(branch.back()->value).value(),
				llvm::ArrayRef(args)
				, branch.size() == 4//可変長引数
			)
		);
		return nullptr;
	}
};

class For :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum {
			INIT,
			COND,
			UPDATA,
			EXPRESSION,
			EXPRESSION_FLAG
		};
		auto loop = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "comp", builder.getBuilder().GetInsertBlock()->getParent());
		auto then = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "loop", builder.getBuilder().GetInsertBlock()->getParent());
		auto update = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "updata", builder.getBuilder().GetInsertBlock()->getParent());
		llvm::BasicBlock* after = nullptr;
		//llvm::Value* result = nullptr;
		std::string result;
		const auto is_named_block = EXPRESSION_FLAG < branch.size();
		if (is_named_block) {

			if (branch.front()->value == "void")after = builder.getPhi().search("for").value().first;
			else {
				if (branch.front()->equal<Var>()) {
					result = branch.front()->branch.front()->value;
				}
				else if (branch.front()->equal<Load>()) {
					result = branch.front()->value;
				}
				if (result.empty()) {
					result = avoid_duplication_with_user_definition("default");
					Var var;
					var.branch.emplace_back(std::make_unique<Node>());
					var.branch.back()->value = result;
					var.branch.emplace_back(std::move(branch.front()));
					var.codegen(builder);

				}
				else {
					branch.front()->codegen(builder);
				}
			}
			branch.erase(branch.begin());
		}
		else {
			builder.scope_nest();
		}
		if (!after) {
			after = llvm::BasicBlock::Create(builder.getBuilder().getContext(), "after", builder.getBuilder().GetInsertBlock()->getParent());
		}
		for (auto& init : branch.front()->branch) {
			init->codegen(builder);
		}

		builder.getBuilder().CreateBr(loop);
		builder.getBuilder().SetInsertPoint(loop);
		if (branch[COND]->branch.size()) {
			builder.getBuilder().CreateCondBr(
				branch[COND]->branch.front()->codegen(builder),
				then,
				after
			);
		}
		else {
			builder.getBuilder().CreateBr(then);
		}
		builder.getBuilder().SetInsertPoint(then);
		branch[EXPRESSION]->codegen(builder);
		if (builder.getBuilder().GetInsertBlock()->getInstList().back().getOpcode() != llvm::Instruction::Br) {
			builder.getBuilder().CreateBr(update);
		}
		builder.getBuilder().SetInsertPoint(update);
		branch[UPDATA]->codegen(builder);
		builder.getBuilder().CreateBr(loop);
		builder.getBuilder().SetInsertPoint(after);
		if (result.size()) {
			Return return_for;
			return_for.branch.emplace_back(std::make_unique<Node>());
			return_for.branch.back()->value = "for";
			return_for.branch.emplace_back(std::make_unique<Load>());
			return_for.branch.back()->branch.emplace_back(std::make_unique<Reference>());
			return_for.branch.back()->branch.back()->value = std::move(result);
			return_for.codegen(builder);
			/*builder.getPhi().push("for", result, after);
			builder.getBuilder().CreateBr(builder.getPhi().search("for").value().first);*/
		}
		if (!is_named_block)builder.scope_break();
		return nullptr;
	}
};
template <auto Function,auto... Default_Args>
class Calculate:public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return (builder.getBuilder().*Function)(branch.front()->codegen(builder), branch.back()->codegen(builder), "",Default_Args...);
	}
};
template <auto F,auto I>
class Compare :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		auto left = branch.front()->codegen(builder);
		if (left->getType()->isFloatingPointTy())return (builder.getBuilder().*F)(left, branch.back()->codegen(builder), "",nullptr);
		return (builder.getBuilder().*I)(left, branch.back()->codegen(builder), "");
	}
};
class String :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		value.pop_back();
		value.erase(value.begin());
		return builder.getBuilder().CreateGlobalStringPtr(value);
	}
};
class StaticArray :public parser::Node{
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		llvm::Value * array_value = builder.getBuilder().CreateAlloca(llvm::ArrayType::get([&builder](this auto self,const auto& branch)->llvm::Type* {
			if(branch.front()->equal<std::remove_reference_t<decltype(*this)>>())return llvm::ArrayType::get(self(branch.front()->branch),branch.size());
			return branch.front()->codegen(builder)->getType();
			}(branch),branch.size()));
		//builder.getModule()->print(llvm::outs(), nullptr);
		/*auto array_type = array_value->getType()->getNonOpaquePointerElementType();
		for (auto index=0; const auto & value : branch) {
			array_value = builder.getBuilder().CreateGEP(
				std::exchange(array_type, array_type->getArrayElementType()),
				array_value,
				{
					llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),0),
					llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),index),
				}
			);
			builder.getBuilder().CreateStore(value->codegen(builder), array_value);
			++index;
		}*/

		[&builder](this auto self,auto& branch,llvm::Value* value,llvm::Type* type)->void{
			for (auto index=0; auto & node: branch) {
				const auto element= builder.getBuilder().CreateGEP(
					type,
					value,
					{
						llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),0),
						llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),index),
					}
				);
				if (node->equal<std::remove_reference_t<decltype(*this)>>()) {
					self(
						node->branch,
						element,
						type->getArrayElementType()
					);
				}
				else {
					builder.getBuilder().CreateStore(node->codegen(builder),element);
				}
				++index;
			}
			}(branch,array_value,array_value->getType()->getNonOpaquePointerElementType());

		return array_value;
		//return nullptr;
		/*const auto last = branch.back()->codegen(builder);
		const auto array_value = builder.getBuilder().CreateAlloca(llvm::ArrayType::get(last->getType(), branch.size()));
		const auto store=[&](const auto index,const auto value) {
			builder.getBuilder().CreateStore(
				value,
				builder.getBuilder().CreateGEP(
					array_value->getType()->getNonOpaquePointerElementType(),
					array_value,
					{
						llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),0),
						llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),index),
					}
					)
			);
		};
		branch.pop_back();
		store(branch.size(), last);
		for (auto i = 0; const auto & item:branch) {
			store(i,item->codegen(builder));
			++i;
		}
		return array_value;*/
	}
};
//多次元配列でエラーになる
class AccessArray :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		auto array_value = branch.front()->codegen(builder);
		auto array_type = array_value->getType();
		branch.erase(branch.begin());
		for (const auto &index : branch) {
			array_value=builder.getBuilder().CreateGEP(
				std::exchange(array_type,array_type->getArrayElementType()),
				array_value,
				{
					llvm::ConstantInt::get(builder.getBuilder().getInt32Ty(),0),
					index->codegen(builder),
				}
			);
		}
		return array_value;
	}
};
class Class :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		auto* struct_type = llvm::StructType::create(builder.getBuilder().getContext(), std::move(branch.front()->value));
		struct_type->setBody({}, false);
		builder.getTypeAnalyzer().emplace(struct_type->getName().str(), struct_type);
		builder.get_namespace().nest(struct_type->getName().str());
		for (auto& function : branch.back()->branch) {
			function->codegen(builder);
		}
		builder.get_namespace().break_path();
		return nullptr;
	}
};
class Var_This :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		auto* value = branch.front()->branch.back()->codegen(builder);
		const auto struct_type = static_cast<llvm::StructType*>(builder.getVariables().search("this").value()->getType()->getNonOpaquePointerElementType());
		builder.getTypeAnalyzer().add_member(
			struct_type->getStructName().str(),
			branch.front()->branch.front()->branch.back()->branch.front()->branch.front()->value

		);
		
		std::vector<llvm::Type*> types(struct_type->getStructNumElements());
		for (auto offset=0; auto & type : types) {
			type = struct_type->getElementType(offset);
			++offset;
		}
		types.push_back(value->getType());
		struct_type->setBody(types,false);
		return branch.front()->codegen(builder);
		//todo:thisを定数にしよう
		//namespaceを管理しているクラスからgetした方が早い
	}
};
class Namespace :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		value = builder.get_namespace().concat(std::move(value));//相対パスとかも
		return nullptr;
	}
};
class Access_Class :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		auto class_value = branch.front()->codegen(builder);
		for (auto& member : branch.back()->branch) {
			if (member->equal<Load>()) {
				class_value=
					builder
					.getBuilder()
					.CreateStructGEP(
						class_value->getType()->getNonOpaquePointerElementType(),
						class_value,
						builder
						.getTypeAnalyzer()
						.search_offset(
							class_value->getType()->getNonOpaquePointerElementType()->getStructName().str(),
							member->branch.front()->value
						).value()
					);
				continue;
			}
			builder.getVariables().scope_nest();
			if([&] {
				if (class_value->getType()->isPointerTy() && class_value->getType()->getNonOpaquePointerElementType()->isStructTy()) {
					if (builder.getModule()->getFunction(member->branch.front()->value.insert(0, class_value->getType()->getNonOpaquePointerElementType()->getStructName().str() + "::"))) {
						return false;
					}
					member->branch.front()->value.erase(0, class_value->getType()->getNonOpaquePointerElementType()->getStructName().str().size() + 2/*::.size*/);
				}
				return true;
				/*
				if (!(class_value->getType()->isPointerTy() && class_value->getType()->getNonOpaquePointerElementType()->isStructTy())) {
					return true;
				}
				else if (builder.getModule()->getFunction(member->branch.front()->value.insert(0, class_value->getType()->getNonOpaquePointerElementType()->getStructName().str() + "::"))) {
					return false;
				}
				member->branch.front()->value.erase(0, class_value->getType()->getNonOpaquePointerElementType()->getStructName().str().size() + 2);//::.size
				return true;
				*/
				}()){
				const auto RECEIVER = std::move(avoid_duplication_with_user_definition("receiver"));
				builder.getVariables().insert_or_assign(
					RECEIVER,
					class_value
				);
				member->branch.back()->branch.emplace(member->branch.back()->branch.begin(),std::make_unique<Load/*referenceでも...?*/>());
				member->branch.back()->branch.front()->branch.emplace(member->branch.back()->branch.front()->branch.begin(),std::make_unique<Reference>());
				member->branch.back()->branch.front()->branch.front()->value = RECEIVER;
			}
			class_value=member->codegen(builder);
			builder.getVariables().scope_break();

		}
		return class_value;
	}
};

int main() {
	enum class TAG {
		DIGIT,
		SNAKE_CASE,
		SNAKE_CAMEL_CASE,
		UPPER_SNAKE_CASE,
		PUBLIC
	};
	build::Builder builder;
	builder.getTypeAnalyzer().emplace("void", builder.getBuilder().getVoidTy());
	builder.getTypeAnalyzer().emplace("d", builder.getBuilder().getDoubleTy());
	builder.getTypeAnalyzer().emplace("f", builder.getBuilder().getFloatTy());
	builder.getTypeAnalyzer().set_callback([&](std::string type) ->std::optional<llvm::Type*>{
		switch (type.front()) {
		case 'u':
		case 'i':
			return builder.getBuilder().getIntNTy(
				std::stoi(type.substr(1))
			);
			break;

		}
		return std::nullopt;
		});
	decltype(parser::Node::branch) nodes;
	auto text = file::File("test.txt").read().value();
	text.push_back('\n');
	for (auto& c : text) {
		auto node = std::make_unique<parser::Node>();
		node.get()->value = std::string(1, c);
		nodes.emplace_back(std::move(node));//todo:Stringのため、この時点でTagを設定しておく
	}
	using BNF = parser::BNF;
	auto digit = BNF("0") | BNF("1") | BNF("2") | BNF("3") | BNF("4") |
		BNF("5") | BNF("6") | BNF("7") | BNF("8") | BNF("9");
	auto upper = BNF("A") | BNF("B") |
		BNF("C") | BNF("D") | BNF("E") | BNF("F") |
		BNF("G") | BNF("H") | BNF("I") | BNF("J") |
		BNF("K") | BNF("L") | BNF("M") | BNF("N") |
		BNF("O") | BNF("P") | BNF("Q") | BNF("R") |
		BNF("S") | BNF("T") | BNF("U") | BNF("V") |
		BNF("W") | BNF("X") | BNF("Y") | BNF("Z");
	auto lower =
		BNF("a") | BNF("b") | BNF("c") | BNF("d") |
		BNF("e") | BNF("f") | BNF("g") | BNF("h") |
		BNF("i") | BNF("j") | BNF("k") | BNF("l") |
		BNF("m") | BNF("n") | BNF("o") | BNF("p") |
		BNF("q") | BNF("r") | BNF("s") | BNF("t") |
		BNF("u") | BNF("v") | BNF("w") | BNF("x") |
		BNF("y") | BNF("z");
	BNF symbol =
		BNF("{") | BNF("}") | BNF("(") | BNF(")") |
		BNF("[")|BNF("]")|
		BNF(";") | BNF(":") | BNF(",") | BNF(".") |
		BNF("&") | BNF("=") | BNF("+") | BNF("-") |
		BNF("*") | BNF("/") | BNF("%") | BNF("<") |
		BNF(">")|BNF("'");
	BNF number = (digit, &number) | digit;
	
	BNF snake_letter = (lower, number) | lower;
	BNF snake_case = (snake_letter, ((BNF("_"), &snake_case) | &snake_case)) | snake_letter;//a1_32を許可するか検討

	BNF upper_snake_letter = (upper, number) | upper;
	BNF upper_snake_case = (upper_snake_letter, ((BNF("_"), &upper_snake_case) | &upper_snake_case)) | upper_snake_letter;//a1_32を許可するか検討
	
	BNF snake_camel_case_letter = (snake_letter, &snake_camel_case_letter) | snake_letter;
	BNF snake_camel_case=(upper,snake_camel_case_letter)|upper;
	snake_camel_case = (snake_camel_case, (BNF("_"), &snake_camel_case)) | snake_camel_case;
	BNF snake_camel_case_guard = (upper, snake_camel_case_letter,BNF("_"),snake_camel_case)|(upper,snake_camel_case_letter);

	BNF until_return = BNF("\n") | (BNF().set<parser::Node>() + ((BNF("\n")) | &until_return));
	BNF until_comment = (BNF("*") + BNF("/")) | (BNF().set<parser::Node>() + ((BNF("*") + BNF("/")) | &until_comment));
	BNF comment = BNF("/") + ((BNF("/") + until_return) | (BNF("*") + until_comment));

	BNF until_quote = BNF("\"") | (((BNF("\\"), BNF("\"")) | (BNF().set<parser::Node>())), (BNF("\"") | &until_quote));
	BNF str = (BNF("\""), until_quote).regist<String>();
	BNF token = comment |
		~(
			str |
			snake_camel_case_guard.regist<Tag<TAG::SNAKE_CAMEL_CASE>>() |
			upper_snake_case.regist<Tag<TAG::UPPER_SNAKE_CASE>>()|//先頭一文字だけに反応している
			snake_case.regist<Tag<TAG::SNAKE_CASE>>() |
			symbol | number.regist<Tag<TAG::DIGIT>>()
			)
		|BNF(" ") |BNF("\n");
	BNF tokens = (token + &tokens) | token;
	nodes = std::move(tokens(nodes).value().get()->branch);
	//for (const auto& node : nodes) {
	//	std::cout << node->value << std::endl;
	//}
	//codegen内部で文字列をnamespaceに応じて変更し、それを使う
	auto ident = BNF().set<Tag<TAG::SNAKE_CASE>>();
	auto constant = BNF().set<Tag<TAG::UPPER_SNAKE_CASE>>();
	BNF class_name = BNF().set<Tag<TAG::SNAKE_CAMEL_CASE>>() | upper;
	BNF scope = (class_name, BNF(":"), BNF(":"), &scope).regist<Namespace>() | ident;
	number = BNF().set<Tag<TAG::DIGIT>>();

	BNF integer = (~number + ~ident/*snake_letter for i32,i64 etc...*/).regist<Int>();
	BNF floating_point = (~(number, BNF("."), number) + (BNF("f").regist<Floating_Point<&llvm::Type::getFloatTy>>() | BNF("d").regist<Floating_Point<&llvm::Type::getDoubleTy>>()));
	BNF expr;

	BNF access_class;
	//BNF lvalue;
	BNF reference = (BNF("&") + ident).regist<Reference>();

	BNF var = (BNF("var") +
		(
			(~(~&access_class + BNF("=") + ~&expr).regist<Assign>()).regist<Var_This>() |
			(
				(
					(~ident + BNF("=") + ~(~&expr).regist<Mutable>()) |
					(~constant + BNF("=") + ~&expr)
					)
				).regist<Var>()
			)
		);

	BNF ret = ((BNF("return") + ~&expr/*ident*/ + ~&expr) | (~BNF("return") + ~&expr) | ~BNF("return")).regist<Return>();
	
	
	BNF if_statement = BNF("if") + BNF("(") + ~&expr + BNF(")") + ~&expr;
	if_statement = ((if_statement + BNF("else") + (~(&if_statement | &expr))) | if_statement).regist<If>();
	BNF if_expression = (~BNF("if") + ~~(BNF("(") + ~&expr + BNF(")") + ~&expr + BNF("else") + (~if_statement | ~&expr)).regist<If>()).regist<Block>();
	BNF comma = (~&expr + BNF(",") + &comma) | ~&expr;
	BNF for_content = ((~BNF(";") | ~comma + BNF(";")) + (~BNF(";") | ~~&expr + BNF(";")) + (~BNF(")") | ~&expr + BNF(")")) + ~&expr).regist<For>();
	BNF for_statement = (~BNF("for") + BNF("(") + ~~(~BNF("void") + ((BNF(",") + for_content) | for_content))).regist<Block>() | BNF("for") + BNF("(") + for_content;
	BNF for_expression = (~BNF("for") + BNF("(") + ~~(~&expr + ((BNF(",") + for_content) | for_content))).regist<Block>();
	//too bad:for(void,;) for(void 0i32;)->OKになるので改善しろ

	BNF static_array = (BNF("[") + comma + BNF("]")).regist<StaticArray>();
	/*todo:
	[
	0i32,
	1i32,//<=このカンマ許可しろ
	]
	*/

	BNF statement = ~(if_statement | for_statement) | (~&expr + BNF(";"));//expr+BNF(";")|expr
	BNF statements = (statement + &statements) | statement;
	BNF block = ((BNF("{") | ~ident + BNF("{")) + (~BNF("}") | (~statements + BNF("}")))).regist < Block >();
	BNF type = ident| class_name;//identは良くない
	BNF define_argument = ~(~type + ~ident);
	define_argument = (define_argument + BNF(",") + &define_argument) | define_argument;
	BNF argument = (~&expr + BNF(",") + &argument) | ~&expr;
	BNF call = (~scope + BNF("(") + ~(BNF(")") | argument + BNF(")"))).regist<Call>();
	

	
	BNF type_specifier = BNF("-") + BNF(">") + ~type;
	BNF function = (BNF("fn") + ~(ident.regist<Namespace>()) + BNF("(") + ~(BNF(")") | (define_argument + BNF(")")))+(~block)).regist<Function>();
	
	//define_class = (~define_class + &define_class) | ~define_class;
	BNF class_content = ~function;
	class_content = (class_content + &class_content) | class_content;
	BNF cls = (BNF("class") + ~class_name + BNF("{")+~class_content+ BNF("}")).regist<Class>();


	BNF variable_length = BNF(".") + BNF(".") + BNF(".");
	BNF extern_argument = (~type + BNF(",") + &extern_argument) | ~type;
	BNF extern_function = (BNF("extern") + ~ident + BNF("(") + ((~variable_length + ~BNF(")")) | ~BNF(")") | (~extern_argument + ((BNF(",") + ~variable_length + BNF(")")) | BNF(")")))) +type_specifier+BNF(";")).regist<Extern>();
	
	
	BNF primary = (BNF("(") + ~~&expr + BNF(")")).regist<Block>();
	expr = BNF().set<String>().regist<String>() | var | ret |static_array|block  | if_expression | for_expression  | reference | call | primary  | (~ident.regist<Reference>()).regist<Load>() | (~constant.regist<Reference>()).regist<Load>() | floating_point | integer;
	
	BNF access_class_nest = (~expr + BNF(".") + &access_class_nest).regist<Access_Class>() | ~expr;
	access_class = (((~ident.regist<Reference>() + BNF(".")) | (~expr + BNF("."))) + ~access_class_nest).regist<Access_Class>();
	expr = (~access_class).regist<Load>() | expr;

	BNF assign = (~(&access_class | ident.regist<Reference>()) + BNF("=") + ~&expr).regist<Assign>();//callもいる
	expr = assign | expr;

	
	BNF mul = (~expr + ((BNF("*") + ~&mul).regist<Calculate<&llvm::IRBuilder<>::CreateMul,false,false>>() | (BNF("/") + ~&mul).regist<Calculate<&llvm::IRBuilder<>::CreateSDiv,false>>() | (BNF("%") + ~&mul).regist<Calculate<&llvm::IRBuilder<>::CreateSRem>>())) | expr;
	expr = mul;
	BNF add = (~expr + ((BNF("+") + ~&add).regist<Calculate<&llvm::IRBuilder<>::CreateAdd,false,false>>() | (BNF("-") + ~&add).regist<Calculate<&llvm::IRBuilder<>::CreateSub,false,false>>())) | expr;
	expr = add;
	//todo:(2 <= 3 <= 4)を許可する
	BNF compare = (
		~expr +
		(
			(BNF("=") + BNF("=") + ~&compare).regist<Compare < &llvm::IRBuilder<>::CreateFCmpOEQ, &llvm::IRBuilder<>::CreateICmpEQ >>() |
			(BNF("!") + BNF("=") + ~&compare).regist<Compare < &llvm::IRBuilder<>::CreateFCmpONE, &llvm::IRBuilder<>::CreateICmpNE >>() |
			(BNF("<") + BNF("=") + ~&compare).regist<Compare < &llvm::IRBuilder<>::CreateFCmpULE, &llvm::IRBuilder<>::CreateICmpULE >>() |
			(BNF(">") + BNF("=") + ~&compare).regist<Compare < &llvm::IRBuilder<>::CreateFCmpUGE, &llvm::IRBuilder<>::CreateICmpUGE >>() |
			(BNF("<") + ~&compare).regist < Compare < &llvm::IRBuilder<>::CreateFCmpULT, &llvm::IRBuilder<>::CreateICmpULT >>() |
			(BNF(">") + ~&compare).regist<Compare < &llvm::IRBuilder<>::CreateFCmpUGT, &llvm::IRBuilder<>::CreateICmpUGT >>()
		)
	) | expr;
	expr = compare;
	BNF access_index = BNF("[") + ~&expr + BNF("]");
	access_index = (access_index + access_index) | access_index;
	BNF access_array = (~expr + access_index).regist<AccessArray>() | expr;
	//[[0i32]][0i32][0i32]をexpr([0i32]access([0i32]))access([0i32])と解釈した方が綺麗
	expr = access_array;

	
	BNF source = (extern_function | function|cls);
	source = ((~source + &source) | ~source);
	BNF source_wrapper = (~source).regist<Block>();

	//source(nodes).value()->codegen(builder);//ここ変えろ
	source_wrapper(nodes).transform([&builder](auto&& node) {
		node->codegen(builder);
		builder.getModule()->print(llvm::outs(), nullptr);
		//std::error_code error_info;
		//llvm::raw_fd_ostream raw_stream("out.ll", error_info,
		//	llvm::sys::fs::OpenFlags::F_None);
		//module->print(raw_stream, nullptr);
		//builder.getModule()->print(llvm::outs(), nullptr);
		llvm::InitializeNativeTarget();
		llvm::InitializeAllAsmPrinters();
		llvm::InitializeAllAsmParsers();
		LLVMLinkInMCJIT();
		auto* func = builder.getModule()->getFunction("main");
		llvm::ValueToValueMapTy vmap;
		llvm::EngineBuilder engineBuilder(std::move(builder.getModule()));
		llvm::ExecutionEngine* engine = engineBuilder.create();
		//engine->runFunction(func, {});
		
		llvm::outs() << engine->runFunction(func, {}).IntVal;
		llvm::outs().flush();
		return node;
		});
	//;

	return EXIT_SUCCESS;
}
