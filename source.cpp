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
			result = child.get()->codegen(builder);
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
class Load :public parser::Node {
public:
	llvm::Value* codegen(build::Builder& builder)override {
		if (builder.getVariables().search(value).value()->getType()->isPointerTy())
			return builder.getBuilder().CreateLoad(
				builder.getVariables().search(value).value()->getType()->getNonOpaquePointerElementType(),
				builder.getVariables().search(value).value()
			);
		return builder.getVariables().search(value).value();
	}
};
class Let :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		enum BRANCH {
			NAME,
			VALUE
		};
		builder.getVariables().insert_or_assign(branch[NAME]->value, branch[VALUE]->codegen(builder));
		//return builder.getVariables().search(branch[NAME]->value).value();
		Load loader;
		loader.value = branch[NAME]->value;
		return loader.codegen(builder);//loadが不要な場面もある
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

class Reference :public parser::Node {
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getVariables().search(value).value();
	}
};
class Assign :public parser::Node {
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
class Float :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return llvm::ConstantFP::get(
			llvm::Type::getFloatTy(builder.getBuilder().getContext()),
			std::stod(branch.front()->value)
		);

	}
};
class Double :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return llvm::ConstantFP::get(
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
				builder.getBuilder().CreateStore(&arg, builder.getVariables().search(branch[ARGUMENTS]->branch[i]->branch[1]->value).value());
			}
			++i;
		}

		branch[BLOCK]->codegen(builder);//block nodeの処理が終わるとret_identのスコープも切れるので、scope_nestをする

		builder.getBuilder().SetInsertPoint(builder.getPhi().search(Return::ret_ident).value().first);
		builder.getBuilder().CreateRet(builder.getPhi().search(Return::ret_ident).value().second.size() ? builder.getPhi().create(builder.getBuilder(), Return::ret_ident) : nullptr);
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
		llvm::Value* result = nullptr;
		//idea:初期化構文が存在したらblockに変形する

		//idea:コンストラクタでnestを呼び出し、デストラクタでbreakを呼び出すクラスを作る
		const auto is_named_block = EXPRESSION_FLAG < branch.size();
		if (is_named_block) {

			if (branch.front()->value == "void")after = builder.getPhi().search("for").value().first;
			else {
				result = branch.front()->codegen(builder);
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
			builder.getBuilder().CreateBr(then);//もしくはcondに1を入れる
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
		if (result) {
			builder.getPhi().push("for", result, after);
			builder.getBuilder().CreateBr(builder.getPhi().search("for").value().first);
		}
		if (!is_named_block)builder.scope_break();
		return nullptr;
	}
};

class Add :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateAdd(branch.front()->codegen(builder), branch.back()->codegen(builder), "");
	}
};
class Sub :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateSub(branch.front()->codegen(builder), branch.back()->codegen(builder), "");
	}
};

class Mul :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateMul(branch.front()->codegen(builder), branch.back()->codegen(builder), "");
	}
};
class Div :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateSDiv(branch.front()->codegen(builder), branch.back()->codegen(builder), "");
	}
};
class Rem :public parser::Node {
private:
public:
	llvm::Value* codegen(build::Builder& builder)override {
		return builder.getBuilder().CreateSRem(branch.front()->codegen(builder), branch.back()->codegen(builder), "");
	}
};
int main() {
	enum class TAG {
		DIGIT,
		SNAKE_CASE
	};
	decltype(parser::Node::branch) nodes;
	auto text = file::File("test.txt").read().value();
	text.push_back('\n');
	for (auto& c : text) {
		auto node = std::make_unique<parser::Node>();
		node.get()->value = std::string(1, c);
		nodes.emplace_back(std::move(node));//todo:Stringのため、この時点でTagを設定しておく
	}
	using BNF = parser::BNF;
	auto digit = BNF("0") | BNF("1") | BNF("2") | BNF("3") | BNF("4") | BNF("5") | BNF("6") | BNF("7") | BNF("8") | BNF("9");
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
		BNF(";") | BNF(":") | BNF(",") | BNF(".") |
		BNF("&") | BNF("=") | BNF("+") | BNF("-") |
		BNF("*") | BNF("/") | BNF("%");
	BNF number = (digit, &number) | digit;
	BNF snake_letter = (lower, number) | lower;
	BNF snake_case = (snake_letter, ((BNF("_"), &snake_case) | &snake_case)) | snake_letter;//a1_32を許可するか検討
	BNF until_return = BNF("\n") | (BNF().set<parser::Node>() + BNF("\n")) | (BNF().set<parser::Node>() + &until_return);
	BNF until_comment = (BNF("*") + BNF("/")) | (BNF().set<parser::Node>() + BNF("*") + BNF("/")) | (BNF().set<parser::Node>() + &until_comment);
	BNF comment = BNF("/") + ((BNF("/") + until_return) | (BNF("*") + until_comment));
	BNF token = ~(snake_case.regist<Tag<TAG::SNAKE_CASE>>() | symbol | number.regist<Tag<TAG::DIGIT>>()) | comment | BNF(" ") | BNF("\n");
	BNF tokens = (token + &tokens) | token;
	nodes = std::move(tokens(nodes).value().get()->branch);
	auto ident = BNF().set<Tag<TAG::SNAKE_CASE>>().regist<Load>();
	number = BNF().set<Tag<TAG::DIGIT>>();

	BNF integer = (~number + ~ident/*snake_letter for i32,i64 etc...*/).regist<Int>();
	BNF floating_point = (~(number, BNF("."), number) + (BNF("f").regist<Float>() | BNF("d").regist<Double>()));
	BNF expr;
	BNF assign = (~ident.regist<Reference>() + BNF("=") + ~&expr).regist<Assign>();
	BNF let = (BNF("let") + ((BNF("mut") + ~ident + BNF("=") + ~(~&expr).regist<Mutable>()) | assign)).regist<Let>();
	BNF reference = (BNF("&") + ident).regist<Reference>();
	BNF ret = ((BNF("return") + ~&expr/*ident*/ + ~&expr) | (~BNF("return") + ~&expr) | ~BNF("return")).regist<Return>();
	BNF if_statement = BNF("if") + BNF("(") + ~&expr + BNF(")") + ~&expr;
	if_statement = ((if_statement + BNF("else") + (~(&if_statement | &expr))) | if_statement).regist<If>();
	BNF if_expression = (~BNF("if") + ~~(BNF("(") + ~&expr + BNF(")") + ~&expr + BNF("else") + (~if_statement | ~&expr)).regist<If>()).regist<Block>();
	BNF for_init = (~&expr + BNF(",") + &for_init) | ~&expr;
	BNF for_content = ((~BNF(";") | ~for_init + BNF(";")) + (~BNF(";") | ~~&expr + BNF(";")) + (~BNF(")") | ~&expr + BNF(")")) + ~&expr).regist<For>();
	BNF for_statement = (~BNF("for") + BNF("(") + ~~(~BNF("void") + ((BNF(",") + for_content) | for_content))).regist<Block>() | BNF("for") + BNF("(") + for_content;
	BNF for_expression = (~BNF("for") + BNF("(") + ~~(~&expr + ((BNF(",") + for_content) | for_content))).regist<Block>();
	//too bad:for(void,;) for(void 0i32;)->OKになるので改善しろ
	BNF statement = ~(if_statement | for_statement) | (~&expr + BNF(";"));//expr+BNF(";")|expr
	BNF statements = (statement + &statements) | statement;
	BNF block = ((BNF("{") | ~ident + BNF("{")) + (~BNF("}") | (~statements + BNF("}")))).regist < Block >();
	BNF type = ident;
	BNF define_argument = ~(~type + ~ident);
	define_argument = (define_argument + BNF(",") + &define_argument) | define_argument;
	BNF argument = (~&expr + BNF(",") + &argument) | ~&expr;
	BNF call = (~ident + BNF("(") + ~(BNF(")") | argument + BNF(")"))).regist<Call>();

	BNF function = (~((BNF("fn") + BNF(":") + type) | BNF("fn")) + ~ident + BNF("(") + ~(BNF(")") | (define_argument + BNF(")"))) + ~block).regist<Function>();
	BNF variable_length = BNF(".") + BNF(".") + BNF(".");
	BNF extern_argument = (~type + BNF(",") + &extern_argument) | ~type;
	BNF extern_function = (BNF("extern") + ~type + ~ident + BNF("(") + ((~variable_length + ~BNF(")")) | ~BNF(")") | (~extern_argument + ((BNF(",") + ~variable_length + BNF(")")) | BNF(")")))) + BNF(";")).regist<Extern>();//上と同じ
	BNF primary = (BNF("(") + ~~&expr + BNF(")")).regist<Block>();
	expr = let | block | ret | if_expression | for_expression | assign | reference | call | primary|ident | floating_point | integer;
	BNF mul = (~expr + ((BNF("*") + ~&mul).regist<Mul>() | (BNF("/") + ~&mul).regist<Div>() | (BNF("%") + ~&mul).regist<Rem>())) | expr;
	expr = mul;
	BNF add = (~expr + ((BNF("+") + ~&add).regist<Add>() | (BNF("-") + ~&add).regist<Sub>())) | expr;
	expr = add;
	BNF source = extern_function | function;
	source = (~((~source + &source) | ~source)).regist<Block>();
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
