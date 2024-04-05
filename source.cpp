#define __ALL_IMPORT__
#if defined(__INTELLISENSE__)
#pragma once
#include "file.cpp"
#include "parser.cpp"
#include <string>
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
		if (NAMED_BLOCK_FLAG/*named block*/<branch.size()) {
			builder.getPhi().init(
				branch[NAME]->value,
				llvm::BasicBlock::Create(builder.getBuilder().getContext(), branch[NAME]->value,//idea:下から一番近いところをfirstとして使う
					builder.getBuilder().GetInsertBlock()->getParent()
				)
			);
		}
		llvm::Value* result;
		for (const auto& child : branch.back()->branch) {
			result = child.get()->codegen(builder);
		}
		
		if (NAMED_BLOCK_FLAG< branch.size()) {
			builder.getBuilder().SetInsertPoint(builder.getPhi().get(branch[NAME]->value).value().first);
			//builder.getBuilder().CreateBr(builder.getPhi().get(branch[NAME]->value).value().first);
			if(builder.getPhi().get(branch[NAME]->value).value().second.size())result = builder.getPhi().create(builder.getBuilder(), branch[NAME]->value);
			
		}

		builder.getVariables().scope_break();
		return result;
	}
};
class Let :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			NAME,
			VALUE
		};
		builder.getVariables().insert_or_assign(branch[NAME]->value, branch[VALUE]->codegen(builder));
		return builder.getVariables().get(branch[NAME]->value).value();
	}
};
class Mutable :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		auto* value = branch.front()->codegen(builder);
		if (value->getType()->isPointerTy())return value;
		auto* variable = builder.getBuilder().CreateAlloca(value->getType(), nullptr, "");
		builder.getBuilder().CreateStore(value, variable);
		return variable;
	}
};
class Load :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		if (builder.getVariables().get(value).value()->getType()->isPointerTy())
			return builder.getBuilder().CreateLoad(
				builder.getVariables().get(value).value()->getType()->getNonOpaquePointerElementType(),
				builder.getVariables().get(value).value()
			);
		return builder.getVariables().get(value).value();
	}
};
class Reference :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getVariables().get(value).value();
	}
};
class Assign :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateStore(branch.back()->codegen(builder), branch.front()->codegen(builder)/*codegen()->to_pointer*/);
	}
};

class INT :public parser::Node {
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
class Floating_Point :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return llvm::ConstantFP::get(
			branch.back()->value == "f" ?
			llvm::Type::getFloatTy(builder.getBuilder().getContext()) :
			llvm::Type::getDoubleTy(builder.getBuilder().getContext()),
			std::stod(branch.front()->value)
		);

	}
};
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
		if (branch.size() == 2&&branch.front()->value==ret_ident && branch.back()->equal<Load>() && builder.getPhi().get(branch.back()->value)) {
			branch.erase(branch.begin());
		}
		if (CODE<branch.size())value = branch.back()->codegen(builder);
		else {
			builder.getBuilder().CreateBr(builder.getPhi().get(branch[NAME]->value).value().first);
			return nullptr;
		}
		if (value->getType()->isIntegerTy(0))return nullptr;
		builder.getPhi().push(branch[NAME]->value,value,builder.getBuilder().GetInsertBlock());
		builder.getBuilder().CreateBr(builder.getPhi().get(branch[NAME]->value).value().first);
		return value;
	}
};
class MyTypeMapper : public llvm::ValueMapTypeRemapper {
private:
	llvm::Type* type;
	bool changed=false;
public:
	MyTypeMapper(decltype(type) type) :type(type) {}
	llvm::Type* remapType(llvm::Type* old) override {
		if (old->isIntegerTy(0)) {
			changed = true;
			return type;
		}
		return old;
	}
	auto &is_changed()const noexcept{
		return changed;
	}
};
class Function :public parser::Node {
private:
	llvm::Type* ret_type;
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			RET_TYPE,
			NAME,
			ARGUMENTS,
			BLOCK
		};
		std::vector<llvm::Type*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = builder.string_to_type(branch[ARGUMENTS]->branch[i]->branch.front()->value).value();
			++i;
		}
		if (!ret_type) {
			ret_type =
				branch[RET_TYPE]->value == "fn" ?
				llvm::Type::getIntNTy(builder.getBuilder().getContext(), 0) :
				builder.string_to_type(branch[RET_TYPE]->value).value();
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
					builder.getBuilder().CreateAlloca(arg.getType(), nullptr, "")
				);
				builder.getBuilder().CreateStore(&arg, builder.getVariables().get(branch[ARGUMENTS]->branch[i]->branch[1]->value).value());
			}
			++i;
		}

		branch[BLOCK]->codegen(builder);//block nodeの処理が終わるとret_identのスコープも切れるので、scope_nestをする
		
		builder.getBuilder().SetInsertPoint(builder.getPhi().get(Return::ret_ident).value().first);
		builder.getBuilder().CreateRet(builder.getPhi().get(Return::ret_ident).value().second.size() ? builder.getPhi().create(builder.getBuilder(), Return::ret_ident) : nullptr);
		builder.getModule()->print(llvm::outs(), nullptr);

		if (builder.getBuilder().GetInsertBlock()->getParent()->getReturnType()->isIntegerTy(0)) {
			ret_type=builder.getPhi().get(Return::ret_ident).value().second.size() ?
				builder.getPhi().get(Return::ret_ident).value().second.front().first->getType() :
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
			if (tm.is_changed()){
				ret_type = builder.getPhi().get(Return::ret_ident).value().second.front().first->getType();
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
		std::vector<llvm::Value*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg:args) {
			arg = branch[ARGUMENTS]->branch[i]->codegen(builder);
			++i;
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
			EXPRESSION_FLAG
		};
		if (EXPRESSION_FLAG < branch.size()) {
			branch.pop_back();
			auto block = std::make_unique<Block>();
			block->branch.emplace_back(std::make_unique<Node>());
			block->branch.front()->value = "if";
			block->branch.emplace_back(std::make_unique<Node>());
			block->branch.back()->branch.emplace_back(std::make_unique<If>());
			block->branch.back()->branch.front()->branch= std::move(branch);
			return block->codegen(builder);
		}
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
		branch[IF]->codegen(builder);
		builder.getBuilder().SetInsertPoint(elseBlock);
		if (ELSE < branch.size())branch[ELSE]->codegen(builder);
		if (elseBlock->getInstList().back().getOpcode() != llvm::Instruction::Br) {
			builder.getBuilder().CreateBr(after);
		}
		if (ELSE < branch.size() && branch[ELSE]->equal<If>()) {
			after->eraseFromParent();
			after = builder.getBuilder().GetInsertBlock();
		}
		if (ifBlock->getInstList().back().getOpcode() != llvm::Instruction::Br) {
			builder.getBuilder().SetInsertPoint(ifBlock);
			builder.getBuilder().CreateBr(after);
		}
		builder.getBuilder().SetInsertPoint(after);
		if (after->getParent()&&!after->getInstList().size()) {
			after->eraseFromParent();
		}
		

		return nullptr;//todo:値を返す
	}
};

class Extern :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		enum {
			TYPE,
			NAME,
			ARGUMENTS
		};
		std::vector<llvm::Type*> args(branch[ARGUMENTS]->branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = builder.string_to_type(branch[ARGUMENTS]->branch[i]->value).value();
			++i;
		}
		builder.getModule()->getOrInsertFunction(
			branch[NAME]->value,
			llvm::FunctionType::get(
				builder.string_to_type(branch[TYPE]->value).value(),
				llvm::ArrayRef(args)
				, branch.size() == 4//可変長引数
			)
		);
		return nullptr;
	}
};

int main() {
	enum class TAG {
		IDENT,
		DIGIT
	};
	decltype(parser::Node::branch) nodes;
	auto text = file::File("test.txt").read().value();
	for (auto& c : text) {
		auto node = std::make_unique<parser::Node>();
		node.get()->value = std::string(1, c);
		nodes.emplace_back(std::move(node));//todo:Stringのため、この時点でTagを設定しておく
	}
	using BNF = parser::BNF;
	auto digit = BNF("0") | BNF("1") | BNF("2") | BNF("3") | BNF("4") | BNF("5") | BNF("6") | BNF("7") | BNF("8") | BNF("9");
	auto alphabet =
		BNF("a") | BNF("b") | BNF("c") | BNF("d") |
		BNF("e") | BNF("f") | BNF("g") | BNF("h") |
		BNF("i") | BNF("j") | BNF("k") | BNF("l") |
		BNF("m") | BNF("n") | BNF("o") | BNF("p") |
		BNF("q") | BNF("r") | BNF("s") | BNF("t") |
		BNF("u") | BNF("v") | BNF("w") | BNF("x") |
		BNF("y") | BNF("z") | BNF("A") | BNF("B") |
		BNF("C") | BNF("D") | BNF("E") | BNF("F") |
		BNF("G") | BNF("H") | BNF("I") | BNF("J") |
		BNF("K") | BNF("L") | BNF("M") | BNF("N") |
		BNF("O") | BNF("P") | BNF("Q") | BNF("R") |
		BNF("S") | BNF("T") | BNF("U") | BNF("V") |
		BNF("W") | BNF("X") | BNF("Y") | BNF("Z");
	BNF ident_first = (alphabet | BNF("_"));
	BNF ident_next = (ident_first | digit);
	ident_next=(ident_next, &ident_next) | ident_next;
	BNF ident = (ident_first, ident_next) | ident_first;
	BNF symbol = BNF("=") | BNF(";") | BNF(".") | BNF("{") | BNF("}") | BNF(";") | BNF("(") | BNF(")") | BNF(",") | BNF("&") | BNF(":");
	BNF number = (digit, &number) | digit;
	BNF token = ~(ident.regist<Tag<TAG::IDENT>>() | symbol | number.regist<Tag<TAG::DIGIT>>()) | BNF(" ") | BNF("\n");
	BNF tokens = (token + &tokens) | token;
	nodes = std::move(tokens(nodes).value().get()->branch);
	//for (const auto& node : source) {
	//	std::cout << node->value << std::endl;
	//}
	//dead idea:functionのブロックをreturn のnamedblockとして扱う->スコープが足りない
	ident = BNF().set<Tag<TAG::IDENT>>().regist<Load>();
	number = BNF().set<Tag<TAG::DIGIT>>();
	BNF integer = (~number + ~ident).regist<INT>();
	BNF floating_point = (~(number, BNF("."), number) + ~(BNF("f") | BNF("d"))).regist<Floating_Point>();
	BNF expr;
	BNF assign = (~ident.regist<Reference>() + BNF("=") + ~&expr).regist<Assign>();
	BNF let = (BNF("let") + ((BNF("mut") + ~ident + BNF("=") + ~(~&expr).regist<Mutable>()) | assign)).regist<Let>();
	BNF reference = (BNF("&") + ident).regist<Reference>();
	BNF ret = ((BNF("return")+~&expr/*ident*/ + ~&expr) |(~BNF("return") + ~&expr) | ~BNF("return")).regist<Return>();//identだが、return namedblock{}を{return,variable,block}と解釈するのでexpr
	BNF if_statement = BNF("if") + BNF("(") + ~&expr + BNF(")") + ~&expr;
	if_statement = ((if_statement + BNF("else")+ (~(&if_statement | &expr))) | if_statement).regist<If>();
	//if_statement = ((if_statement + BNF("else") + ((~(&if_statement | &expr) + ~BNF(";")) | (~(&if_statement | &expr)))) | if_statement).regist<If>();
	BNF if_expression = (if_statement + ~BNF(";")).regist<If>();
	BNF statement = (~&expr + BNF(";"))| ~&expr;//expr+BNF(";")|expr
	BNF statements = (statement + &statements) | statement;
	BNF block = ((BNF("{")|~ident+BNF("{")) + (~BNF("}") | (~statements + BNF("}")))).regist < Block >();
	BNF type = ident;
	BNF define_argument = ~(~type + ~ident);
	define_argument= (define_argument + BNF(",") + &define_argument) | define_argument;
	BNF argument = (~&expr + BNF(",") + &argument) | ~&expr;
	BNF call = (~ident + BNF("(") + ~(BNF(")") | argument + BNF(")"))).regist<Call>();

	BNF function = (~((BNF("fn") + BNF(":") + type) | BNF("fn")) + ~ident + BNF("(") + ~(BNF(")") | (define_argument + BNF(")"))) + ~block).regist<Function>();
	BNF variable_length = BNF(".") + BNF(".")+BNF(".");
	BNF extern_argument = (~type + BNF(",") + &extern_argument) | ~type;
	BNF extern_function = (BNF("extern") + ~type+~ident + BNF("(") + ((~variable_length + ~BNF(")")) |~BNF(")") | (~extern_argument + ((BNF(",")+~variable_length+BNF(")"))|BNF(")")))) + BNF(";")).regist<Extern>();//上と同じ
	expr = let | block|ret |if_expression|if_statement|floating_point | integer | assign | reference  | call | ident;
	BNF source=extern_function|function;
	source=(~((~source + &source) | ~source)).regist<Block>();
	build::Builder builder;
	//source(nodes).value()->codegen(builder);//ここ変えろ
	source(nodes).transform([&builder](auto&& node) {
		node->codegen(builder);
		//std::error_code error_info;
		//llvm::raw_fd_ostream raw_stream("out.ll", error_info,
		//	llvm::sys::fs::OpenFlags::F_None);
		//module->print(raw_stream, nullptr);
		builder.getModule()->print(llvm::outs(), nullptr);
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

	return EXIT_SUCCESS;
}