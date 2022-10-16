#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/IR/IRBuilder.h"    
#include "llvm/IR/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"
#include <memory>
#include <string>
#include <functional>
#include <iostream>
#include <any>
#include <regex>
#include <unordered_map>
enum class TOKEN {
	T_EOF,
	NUMBER,
	STRING,
	IDENT,
	RESERVED,
};
class Lexer {
private:
public:
	using tokensT = std::vector<std::pair<TOKEN, std::string> >;
	auto tokenize(std::string str) {
		tokensT data;
		while (str.size()) {
			auto check = [&](const auto token, const auto regex) {
				std::smatch m;
				if (!std::regex_search(str, m, std::regex(regex)))return false;
				data.push_back({ token,m[0].str() });
				str = m.suffix();
				return true;
			};
			if (
				check(TOKEN::NUMBER, R"(^\d+)") ||
				check(TOKEN::RESERVED, R"(^([;,\.\(\)+=\-<>{}]))") ||
				check(TOKEN::IDENT, R"(^[a-zA-Z_][\w]*)") ||
				check(TOKEN::STRING, "^\".*?[^\\\\]\"")
				) {
				continue;
			}
			str.erase(str.begin());
		}
		data.push_back({ TOKEN::T_EOF,"" });
		return data;
	}

};
enum class NODE {
	NONE,
	SOME,
	NUMBER,
	ADD,
	FUNCTION,
	BLOCK,
	RETURN,
	EXTERN,
	CALL,
	VARIABLE,
	ASSIGN,
	IF,
	DECLARE,
	LOAD,
	WHILE,
	LESS
};
class Node {
private:
public:
	NODE node = NODE::NONE;
	std::string value;
	std::vector<Node> branch;
};
class BNF {
private:
	using Iter = Lexer::tokensT::iterator&;
	std::function<Node(Iter)> parser;
public:
	BNF() {
		parser = [](Iter) {return Node(); };
	}
	BNF(decltype(parser) parser) :parser(parser) {}
	BNF(TOKEN token) {
		parser = [token = std::move(token)](Iter iter) {
			Node node;
			if (iter->first != token)return node;
			node.node = NODE::SOME;
			node.value = iter->second;
			++iter;
			return node;
		};
	}
	BNF(std::string str) {
		parser = [str = std::move(str)](Iter iter) {
			Node node;
			if (iter->second != str)return node;
			node.node = NODE::SOME;
			node.value = iter->second;
			++iter;
			return node;
		};
	}
	auto expect(BNF bnf) {
		return BNF([selfParser = this->parser, parser = bnf.parser](Iter iter) {
			auto node = selfParser(iter);
			if (node.node == NODE::NONE)return node;
			if (parser(iter).node == NODE::NONE)node.node = NODE::NONE;
			return node;
			});
	}
	auto regist(NODE node) {
		parser = [parser = std::move(parser), value = std::move(node)](Iter iter) {
			auto node = parser(iter);
			if (node.node == NODE::NONE)return node;
			node.node = value;
			return node;
		};
		return *this;
	}
	auto operator+(BNF bnf) {
		return BNF([selfParser = this->parser, parser = std::move(bnf.parser)](Iter iter) {
			auto temp = iter;
			auto node = selfParser(iter);
			if (node.node == NODE::NONE) {
				iter = temp;
				return node;
			}
			auto branch = std::move(node.branch);
			node = parser(iter);
			if (node.node == NODE::NONE) {
				iter = temp;
				return node;
			}
			node.branch.insert(node.branch.begin(), branch.begin(), branch.end());
			return node;
			});
	}
	auto operator|(BNF bnf) {
		return BNF([selfParser = this->parser, parser = bnf.parser](Iter iter) {
			auto node = selfParser(iter);
			if (node.node != NODE::NONE)return node;
			return parser(iter);
			});
	}
	auto operator()(Iter iter) {
		return parser(iter);
	}
	auto push() {
		return BNF([parser = this->parser](Iter iter) {
			Node node;
			auto child = parser(iter);
			if (child.node == NODE::NONE)return node;
			node.node = NODE::SOME;
			node.branch.push_back(child);
			return node;
			});
	}
	auto loop() {
		return BNF([parser = this->parser](Iter iter) {
			auto node = parser(iter);
			if (node.node == NODE::NONE)return  node;
			auto branch = node.branch;
			Node before;
			while ((before = parser(iter)).node != NODE::NONE) {
				node = before;
				node.branch.insert(node.branch.begin(), branch.begin(), branch.end());
				branch = node.branch;
			}
			return node;
			});
	}
	auto operator*() {
		return BNF([this](Iter iter) {
			return this->parser(iter);
			});
	}
	auto operator[](BNF bnf) {
		return BNF([selfParser = this->parser, parser = bnf.parser](Iter iter) {
			auto node = selfParser(iter);
			if (node.node == NODE::NONE)return node;
			auto ifAny = parser(iter);
			if (ifAny.node == NODE::NONE)return node;
			ifAny.branch.insert(ifAny.branch.begin(), node.branch.begin(), node.branch.end());
			return ifAny;
			});
	}
};
class Generator {
private:
	llvm::LLVMContext context;
	std::unique_ptr<llvm::Module> mainModule;
	llvm::IRBuilder<> builder;
	std::unordered_map<std::string, llvm::Value*> variables;//variable name->obj
public:
	Generator() :
		mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
		builder(context)
	{

	}
	llvm::Value *codegen(Node node) {
		switch (node.node) {
		case NODE::BLOCK:
			for (const auto& child : node.branch) {
				codegen(child);
			}
			break;
		case NODE::EXTERN:
			mainModule->getOrInsertFunction(
				node.branch[0/*function name*/].value,//function name
				llvm::FunctionType::get(llvm::Type::getDoubleTy(context),//return type
					llvm::ArrayRef(std::vector<llvm::Type*>(node.branch[1/*arguments type*/].branch.size(), builder.getDoubleTy()))
					, false));//可変長
			break;
		case NODE::FUNCTION:
			variables.clear();
			builder.SetInsertPoint(llvm::BasicBlock::Create(context, "entry",
				llvm::Function::Create(
					llvm::FunctionType::get(llvm::Type::getDoubleTy(context),
						llvm::ArrayRef(std::vector<llvm::Type*>(node.branch[1/*arguments type*/].branch.size(), builder.getDoubleTy())), false),
					llvm::Function::ExternalLinkage, node.branch[0/*function name*/].value, *mainModule)
			));
			for (auto i=0; auto & arg : mainModule->getFunction(node.branch[0].value)->args()) {
				variables.emplace(node.branch[1].branch[i].branch[1].value, &arg);
			}
			codegen(node.branch[2/*block*/]);
			break;
		case NODE::RETURN:
			builder.CreateRet(codegen(node.branch[0/*expression*/]));
			break;
		case NODE::NUMBER:
			return llvm::ConstantFP::get(context, llvm::APFloat(std::stod(node.value)));
			break;
		case NODE::ADD:
			return builder.CreateFAdd(codegen(node.branch[0]), codegen(node.branch[1]), "addtmp");
			break;
		case NODE::LOAD:
			return builder.CreateLoad(builder.getDoubleTy(), codegen(node.branch[0/*expression*/]));
			break;
		case NODE::VARIABLE:
			//return builder.CreateLoad(builder.getDoubleTy(), variables[node.value]);
			return variables[node.value];
			break;
		case NODE::ASSIGN:
			return builder.CreateStore(codegen(node.branch[1]),codegen(node.branch[0]));
			break;
		case NODE::DECLARE:
			variables.emplace(node.branch[1].branch[0].value,builder.CreateAlloca(builder.getDoubleTy(), nullptr, node.branch[1].branch[0].value));
			return codegen(node.branch[1]);
			break;
		case NODE::LESS:
			return builder.CreateUIToFP(builder.CreateFCmpULT(codegen(node.branch[0]), codegen(node.branch[1]), "compareTemp"),builder.getDoubleTy(), "boolTemp");
			break;
		case NODE::IF:
		{
			Node zero;
			zero.value = "0";
			zero.node = NODE::NUMBER;
			auto* function = builder.GetInsertBlock()->getParent();
			auto *then = llvm::BasicBlock::Create(context, "then", function);
			auto* elseB = llvm::BasicBlock::Create(context, "else");
			auto* merge = llvm::BasicBlock::Create(context, "ifcont");
			builder.CreateCondBr(
				builder.CreateFCmpONE(codegen(node.branch[0].branch[0]), codegen(zero), "ifcond"),
				then,
				elseB
			);
			builder.SetInsertPoint(then);
			codegen(node.branch[0].branch[1]);
			builder.CreateBr(merge);
			then = builder.GetInsertBlock();

			function->getBasicBlockList().push_back(elseB);
			builder.SetInsertPoint(elseB);
			codegen(node.branch[1]);
			builder.CreateBr(merge);
			elseB = builder.GetInsertBlock();
			
			function->getBasicBlockList().push_back(merge);
			builder.SetInsertPoint(merge);
		}
			break;
		case NODE::WHILE:
		{
			Node zero;
			zero.value = "0";
			zero.node = NODE::NUMBER;
			auto* function = builder.GetInsertBlock()->getParent();
			auto* loop = llvm::BasicBlock::Create(context, "loop", function);
			auto* after = llvm::BasicBlock::Create(context,"afterLoop");
			builder.CreateCondBr(
				builder.CreateFCmpONE(codegen(node.branch[0]), codegen(zero), "loop"),
				loop,
				after
			);
			builder.SetInsertPoint(loop);
			codegen(node.branch[1]);
			builder.CreateCondBr(
				builder.CreateFCmpONE(codegen(node.branch[0]), codegen(zero), "loop"),
				loop,
				after
			);

			function->getBasicBlockList().push_back(after);
			builder.SetInsertPoint(after);
		}
			break;
		case NODE::CALL:
		{
			std::vector<llvm::Value*> args(node.branch[1].branch.size());
			for (auto i = 0; auto & arg:args) {
				arg = codegen(node.branch[1].branch[i]);
			}
			return builder.CreateCall(mainModule->getFunction(any_cast<std::string>(node.branch[0].value)), args);
		}
			break;
		}
	}
	auto &getModule() {
		return mainModule;
	}
};
class JIT {
private:
	llvm::ExecutionEngine *engine;
	llvm::Function* func;
public:
	JIT(std::unique_ptr<llvm::Module> &mainModule) {
		llvm::InitializeNativeTarget();
		llvm::InitializeAllAsmPrinters();
		llvm::InitializeAllAsmParsers();
		LLVMLinkInMCJIT();
		func = mainModule->getFunction("main");
		llvm::EngineBuilder engineBuilder(std::move(mainModule));
		engine = engineBuilder.create();
	}
	auto run() {
		return std::move(engine->runFunction(func, {}));
	}
};
int main() {
	auto tokens = Lexer().tokenize("fn main(){double x=0;while x.load<10{x=x.load+1;};return x.load;}");
	auto iter = tokens.begin();
	auto number = BNF(TOKEN::NUMBER).regist(NODE::NUMBER);
	auto variable = BNF(TOKEN::IDENT).regist(NODE::VARIABLE);
	BNF expr;
	auto load = (variable.push() + BNF(".") + BNF("load")).regist(NODE::LOAD);
	auto call = (BNF(TOKEN::IDENT).push() + BNF("(")[(*expr).push()[BNF(",")].loop()].push() + BNF(")")).regist(NODE::CALL);
	auto add = (number|call|load|variable).push() + (BNF("+") + (*expr).push().regist(NODE::ADD)).loop().regist(NODE::ADD);
	auto less = ((add|number | call | load | variable).push() + BNF("<") + (*expr).push()).regist(NODE::LESS);
	auto assign = ((variable|call).push() + BNF("=") + (*expr).push()).regist(NODE::ASSIGN);
	BNF ret,ifExpr,forExpr,whileExpr;
	auto declare = (BNF(TOKEN::IDENT).push() + assign.push()).regist(NODE::DECLARE);
	expr =  add|less|number|*ret|call|*ifExpr|*forExpr|*whileExpr|declare|load|assign|variable;
	ret = (BNF("return") + expr.push()).regist(NODE::RETURN);
	auto block = (BNF("{") + expr.expect(BNF(";")).push().loop() + BNF("}")).regist(NODE::BLOCK);
	ifExpr = ((BNF("if")+expr.push() + block.push()).push()[(BNF("else") + BNF("if") + expr.push() + block.push()).push().loop()][BNF("else") + block.push()]).regist(NODE::IF);
	whileExpr = (BNF("while") + expr.push() + block.push()).regist(NODE::WHILE);
	auto externFunc = (BNF("extern") + BNF(TOKEN::IDENT).push() + BNF("(")[BNF(TOKEN::IDENT).push()[BNF(",")].loop()].push() + BNF(")") + BNF(";")).regist(NODE::EXTERN);
	auto func = (BNF("fn") + BNF(TOKEN::IDENT).push() + BNF("(")[(BNF(TOKEN::IDENT).push() + BNF(TOKEN::IDENT).push())[BNF(",")].push().loop()].push() + BNF(")") + block.push()).regist(NODE::FUNCTION);
	auto program = (externFunc | func).push().regist(NODE::BLOCK).loop();
	Generator generator;
	generator.codegen(program(iter));
	generator.getModule()->print(llvm::outs(),nullptr);
	JIT engine(generator.getModule());
	llvm::outs()<<(int)engine.run().DoubleVal;
	llvm::outs().flush();
	return EXIT_SUCCESS;
}
