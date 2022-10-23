#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/IR/IRBuilder.h"    
#include "llvm/IR/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"
#include <stack>
#include <memory>
#include <string>
#include <sstream>
#include <functional>
#include <iostream>
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
				check(TOKEN::RESERVED, R"(^([&\[\];,\.\(\)+*/=\-<>{}]))") ||
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
	WHILE,
	LESS,
	LET,
	SUB,
	MUL,
	DIV,
	INT,
	FLOATING_POINT,
	ARRAY,
	ARRAY_ACCESS,
	REFERENCE,
	STRUCT,
	STRUCT_INIT,
	MEMBER,
	LOAD
};
class Node {
private:
public:
	NODE node = NODE::NONE;
	std::string value;
	std::vector<Node> branch;
	auto linkBranchStr() {
		std::string str;
		for (auto& child : branch) {
			str += child.value;
		}
		return str;
	}
};
class BNF {
private:
	using Iter = Lexer::tokensT::iterator&;
	std::function<Node(Iter)> parser;
public:
	BNF() {
		parser = [](Iter) {
			Node node;
			node.node = NODE::SOME;
			return node;
		};
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
		return BNF([parser=this->parser,value=std::move(node)](Iter iter) {
			auto node = parser(iter);
			if (node.node == NODE::NONE)return node;
			node.node = value;
			return node;
			});
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
class Type {
private:
	std::unordered_map<std::string, llvm::Type*> types;
	std::function<decltype(types)::mapped_type(std::string)> analyze;
public:
	Type(llvm::IRBuilder<>& builder) {
		types = {
				{"double", builder.getDoubleTy()},
				{ "float",builder.getFloatTy() },
				{ "bool",builder.getInt1Ty() },
				{ "void",builder.getVoidTy() },
		};
		analyze = [&](std::string str)->llvm::Type* {
			const auto pointer = str.size() - str.find_last_not_of('*') - 1;
			str.erase(str.size() - pointer);
			auto type = [&]()->llvm::Type* {
				if (types.count(str)) {
					return types[str];
				}
				else if (str.front() == 'i') {
					return builder.getIntNTy(std::stoi(str.substr(1)));
				}
				return builder.getVoidTy();
			}();
			for (auto i = 0; i < pointer; ++i) {
				type = type->getPointerTo();
			}
			return type;
		};
	}
	auto emplace(decltype(types)::key_type key,decltype(types)::mapped_type value) {
		types.emplace(key,value);
	}
	auto operator()(std::string str) {
		return analyze(str);
	}
};
class CodeGenerator;
class Codegen {
private:
public:
	virtual llvm::Value* codegen(CodeGenerator&,Node) = 0;
};
class CodeGenerator {
private:
	std::unordered_map<NODE, std::unique_ptr<Codegen> > generators;
	llvm::LLVMContext context;
	std::unique_ptr<llvm::Module> mainModule;
	llvm::IRBuilder<> builder;
	Type typeAnalyzer;
	llvm::Type* retType;
	std::unordered_map<std::string, llvm::AllocaInst*> variables;
	std::unordered_map<std::string, std::unordered_map<std::string, unsigned> > structMember;
public:
	CodeGenerator() :
		mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
		builder(context),
		typeAnalyzer(builder)
	{

	}
	auto& getStructMember() {
		return structMember;
	}
	auto& getVariables() {
		return variables;
	}
	auto& getType() {
		return typeAnalyzer;
	}
	auto& getRetType() {
		return retType;
	}
	auto& getModule() {
		return mainModule;
	}
	template <class T>
	auto emplace(decltype(generators)::key_type key) {
		generators.emplace(key, std::make_unique<T>());
	}
	auto& getBuilder() {
		return builder;
	}
	llvm::Value* codegen(Node node) {
		return generators[node.node]->codegen(*this, node);
	}
};
class AddNode :public Codegen{//todo:template add sub mul div
public:
	llvm::Value* codegen(CodeGenerator &cg,Node node)override{
		return cg.getBuilder().CreateFAdd(cg.codegen(node.branch[0]), cg.codegen(node.branch[1]), "addtmp");
	}
};
class SubNode :public Codegen {
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateFSub(cg.codegen(node.branch[0]), cg.codegen(node.branch[1]), "subtmp");
	}
};
class MulNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateMul(cg.codegen(node.branch[0]), cg.codegen(node.branch[1]), "multmp");
	}
};
class DivNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateFDiv(cg.codegen(node.branch[0]), cg.codegen(node.branch[1]), "divtmp");
	}
};
class LessNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateUIToFP(
			cg.getBuilder().CreateFCmpULT(
				cg.codegen(node.branch[0]),
				cg.codegen(node.branch[1]),
				"compareTemp"),
			cg.getBuilder().getDoubleTy(), "boolTemp");
	}
};

class DoubleNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return llvm::ConstantFP::get(cg.getBuilder().getContext(), llvm::APFloat(std::stod(node.linkBranchStr())));
	}
};
class IntNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return llvm::ConstantInt::get(
			cg.getBuilder().getContext(),
			llvm::APInt(
				std::stoi(node.branch[1].value.substr(1)),
				std::stoi(node.branch[0].value),
				node.branch[1].value.front() == 'u'
			)
		);
	}
};
class StructNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* structType = llvm::StructType::create(cg.getBuilder().getContext(), node.branch[0].value);
		cg.getType().emplace(structType->getName().str(), structType);
		std::vector <llvm::Type* > types(node.branch[1].branch.size());
		cg.getStructMember().emplace(structType->getName().str(),std::unordered_map<std::string,unsigned>{});
		for (unsigned i = 0; auto & type : types) {
			type = cg.getType()(node.branch[1].branch[i].branch[0].linkBranchStr());
			cg.getStructMember()[structType->getName().str()].emplace(node.branch[1].branch[i].branch[1].value, i);
			++i;
		}
		structType->setBody(types, false);
	}
};
class MemberNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables()[node.branch[0].value]->getAllocatedType()->getStructElementType(cg.getStructMember()[node.branch[0].value][node.branch[1].value]),
			cg.getBuilder().CreateStructGEP(
				cg.getVariables()[node.branch[0].value]->getAllocatedType(),
				cg.getVariables()[node.branch[0].value],
				cg.getStructMember()[node.branch[0].value][node.branch[1].value]
			)
		);
	}
};
class ArrayAccessNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables()[node.branch[0].value]->getAllocatedType()->getArrayElementType(),
			cg.getBuilder().CreateGEP(
				cg.getVariables()[node.branch[0].value]->getAllocatedType(),
				cg.getVariables()[node.branch[0].value],
				{
					llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
					cg.codegen(node.branch[1]),
				}
				)
		);
	}
};
class VariableNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables()[node.value]->getAllocatedType(),
			cg.getVariables()[node.value]
		);
	}
};
class ReferenceNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getVariables()[node.value];
	}
};
class LetNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		if (node.branch[1].node == NODE::ARRAY) {
			auto* value = cg.codegen(node.branch[1].branch[0]);
			auto* arrayValue = cg.getBuilder().CreateAlloca(llvm::ArrayType::get(value->getType(), node.branch[1].branch.size()));
			for (auto i = 0; i < node.branch[1].branch.size(); ++i) {
				cg.getBuilder().CreateStore(
					cg.codegen(node.branch[1].branch[i]),
					cg.getBuilder().CreateGEP(
						arrayValue->getAllocatedType(),
						arrayValue,
						{
							llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
							llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),i),
						}
						)
				);
			}
			cg.getVariables().emplace(node.branch[0].value, arrayValue);
			return cg.getVariables()[node.branch[0].value];
		}
		else if (node.branch[1].node == NODE::STRUCT_INIT) {
			cg.getVariables().emplace(node.branch[0].value, cg.getBuilder().CreateAlloca(cg.getType()(node.branch[1].branch[0].value)));
			for (auto i = 0; auto & value:node.branch[1].branch[1].branch) {
				cg.getBuilder().CreateStore(
					cg.codegen(value),
					cg.getBuilder().CreateStructGEP(cg.getVariables()[node.branch[0].value]->getAllocatedType(), cg.getVariables()[node.branch[0].value], i)
				);
				++i;
			}
			return cg.getVariables()[node.branch[0].value];
		}
		auto* value = cg.codegen(node.branch[1]);
		cg.getVariables().emplace(
			node.branch[0].value,
			cg.getBuilder().CreateAlloca(value->getType(), nullptr, node.branch[0].value)
		);
		return cg.getBuilder().CreateStore(value, cg.getVariables()[node.branch[0].value]);
	}
};
class AssignNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateStore(
			cg.codegen(node.branch[1]),
			[&]()->llvm::Value* {
				if (node.branch[0].node == NODE::VARIABLE)return cg.getVariables()[node.branch[0].value];
				else if (node.branch[0].node == NODE::MEMBER) {
					return 	cg.getBuilder().CreateStructGEP(
						cg.getVariables()[node.branch[0].branch[0].value]->getAllocatedType(),
						cg.getVariables()[node.branch[0].branch[0].value],
						cg.getStructMember()[node.branch[0].branch[0].value][node.branch[0].branch[1].value]
					);
				}
				return cg.getBuilder().CreateGEP(
					cg.getVariables()[node.branch[0].branch[0].value]->getAllocatedType(),
					cg.getVariables()[node.branch[0].branch[0].value],
					{
						llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
						cg.codegen(node.branch[0].branch[1]),
					}
				);
			}()
				);
	}
};
class BlockNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		llvm::Value* result;
		for (const auto& child : node.branch) {
			result = cg.codegen(child);
		}
		return result;
	}
};
class IfNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::BasicBlock*> blocks;
		for (auto i = 0; i <= node.branch.size(); ++i) {
			blocks.push_back(llvm::BasicBlock::Create(cg.getBuilder().getContext(), "ifBlock", cg.getBuilder().GetInsertBlock()->getParent()));
		}
		llvm::BasicBlock* before;
		for (auto i = 0; i < blocks.size() - 1 - (node.branch[node.branch.size() - 1].branch.size() == 1); ++i) {
			before = node.branch.size() == 1 ? blocks.back() : llvm::BasicBlock::Create(cg.getBuilder().getContext(), "branch", cg.getBuilder().GetInsertBlock()->getParent());
			cg.getBuilder().CreateCondBr(
				cg.getBuilder().CreateFCmpONE(cg.codegen(node.branch[i].branch[0]), llvm::ConstantFP::get(cg.getBuilder().getContext(), llvm::APFloat(0.0)), "ifcond"),
				blocks[i],
				before
			);
			cg.getBuilder().SetInsertPoint(before);
		}
		if (node.branch[node.branch.size() - 1].branch.size() == 1) {
			cg.getBuilder().CreateBr(blocks[blocks.size() - 2]);
		}
		for (auto i = 0; i < blocks.size() - 1 - (node.branch[node.branch.size() - 1].branch.size() == 1); ++i) {
			cg.getBuilder().SetInsertPoint(blocks[i]);
			cg.codegen(node.branch[i].branch[1]);
			cg.getBuilder().CreateBr(blocks.back());
		}
		if (node.branch[node.branch.size() - 1].branch.size() == 1) {
			cg.getBuilder().SetInsertPoint(blocks[blocks.size() - 2]);
			cg.codegen(node.branch[node.branch.size() - 1]);
			cg.getBuilder().CreateBr(blocks.back());
		}
		cg.getBuilder().SetInsertPoint(blocks.back());
	}
};
class WhileNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* loop = llvm::BasicBlock::Create(cg.getBuilder().getContext(), "loop", cg.getBuilder().GetInsertBlock()->getParent());
		auto* then = llvm::BasicBlock::Create(cg.getBuilder().getContext(), "then", cg.getBuilder().GetInsertBlock()->getParent());
		auto* after = llvm::BasicBlock::Create(cg.getBuilder().getContext(), "afterLoop", cg.getBuilder().GetInsertBlock()->getParent());
		cg.getBuilder().CreateBr(loop);
		cg.getBuilder().SetInsertPoint(loop);
		cg.getBuilder().CreateCondBr(
			cg.getBuilder().CreateFCmpONE(cg.codegen(node.branch[0]), llvm::ConstantFP::get(cg.getBuilder().getContext(), llvm::APFloat(0.0)), "loopCond"),
			then,
			after
		);
		cg.getBuilder().SetInsertPoint(then);
		cg.codegen(node.branch[1]);
		cg.getBuilder().CreateBr(loop);
		cg.getBuilder().SetInsertPoint(after);
	}
};
class RetNode:public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg,Node node)override {
		auto* value = cg.codegen(node.branch[0/*expression*/]);
		cg.getRetType()= value->getType();//todo:継承の度合いが一番高いのを返り値にする
		cg.getBuilder().CreateRet(value);
	}
};
class FunctionNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Type*> args(node.branch[1].branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = cg.getType()(node.branch[1].branch[i].branch[0].linkBranchStr());
			++i;
		}
		auto createFunction = [&]() {
			cg.getVariables().clear();
			cg.getBuilder().SetInsertPoint(llvm::BasicBlock::Create(cg.getBuilder().getContext(), "entry",
				llvm::Function::Create(
					llvm::FunctionType::get(cg.getRetType(),//retType=builder.getVoidTy(),
						llvm::ArrayRef(args), false),
					llvm::Function::ExternalLinkage, node.branch[0/*function name*/].value, *cg.getModule())
			));
			for (auto i = 0; auto & arg : cg.getModule()->getFunction(node.branch[0/*function name*/].value)->args()) {
				cg.getVariables().emplace(
					node.branch[1].branch[i].branch[1].value,
					cg.getBuilder().CreateAlloca(arg.getType(), nullptr, node.branch[1].branch[i].branch[1].value)
				);
				cg.getBuilder().CreateStore(&arg, cg.getVariables()[node.branch[1].branch[i].branch[1].value]);
				++i;
			}
			cg.codegen(node.branch[2/*block*/]);
		};
		cg.getRetType() = cg.getBuilder().getVoidTy();
		createFunction();
		cg.getModule()->getFunction(node.branch[0].value)->eraseFromParent();
		createFunction();
	}
};
class ExternNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Type*> args(node.branch[2].branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = cg.getType()(node.branch[2].branch[i].linkBranchStr());
			++i;
		}
		cg.getModule()->getOrInsertFunction(
			node.branch[1/*function name*/].value,//function name
			llvm::FunctionType::get(
				cg.getType()(node.branch[0].value),//return type
				llvm::ArrayRef(args)
				, false
			)
		);
	}
};
class CallNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Value*> args(node.branch[1].branch.size());
		for (auto i = 0; auto & arg:args) {
			arg = cg.codegen(node.branch[1].branch[i]);
		}
		return cg.getBuilder().CreateCall(cg.getModule()->getFunction(node.branch[0].value), args);
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
	auto tokens = Lexer().tokenize("fn main(){return 10.0;}");
	auto iter = tokens.begin();
	auto number = BNF(TOKEN::NUMBER).regist(NODE::NUMBER);
	auto type = BNF(TOKEN::IDENT).push()[BNF("*").push().loop()];
	auto variable = BNF(TOKEN::IDENT).regist(NODE::VARIABLE);
	auto floatNum = (number.push() + BNF(".").push() + number.push()).regist(NODE::FLOATING_POINT);//.number|f
	auto intNum = (number.push()+BNF(TOKEN::IDENT).push()).regist(NODE::INT);
	BNF expr;
	auto call = (BNF(TOKEN::IDENT).push() + BNF("(")[(*expr).push()[BNF(",")].loop()].push() + BNF(")")).regist(NODE::CALL);
	auto member = ((variable|call).push() + (BNF(".") + (variable | call).push().loop())).regist(NODE::MEMBER);
	BNF mul, add;
	auto compare = ((*add).push() + BNF("<") + (*add).push()).regist(NODE::LESS) | (*add);
	auto let = (BNF("let") + BNF(TOKEN::IDENT).push() + BNF("=") + compare.push()).regist(NODE::LET);
	auto reference = (BNF("&") + variable).regist(NODE::REFERENCE);
	auto arrayAccess = (variable.push() + BNF("[") + (*expr).push() + BNF("]")).regist(NODE::ARRAY_ACCESS);
	auto assign = ((arrayAccess|member|variable).push() + BNF("=") + (*expr).push()).regist(NODE::ASSIGN);
	auto arrayExpr = (BNF("[") + ((*expr).push()[BNF(",")]).loop() + BNF("]")).regist(NODE::ARRAY);
	auto structInit = (BNF(TOKEN::IDENT).push()+BNF("{")+((*expr)[BNF(",")]).push().loop().push() + BNF("}")).regist(NODE::STRUCT_INIT);//ident(member)+expr
	auto primary = BNF("(")+(*compare).expect(BNF(")")) | intNum|floatNum| structInit|arrayExpr|arrayAccess|member|call|reference|variable;
	mul = (primary.push()+(BNF("*") + (*primary).push()).regist(NODE::MUL) | BNF("/") + (*primary).push().regist(NODE::DIV)) | primary;
	add =( mul.push() + (BNF("+") + (*add).push()).regist(NODE::ADD) | BNF("-") + (*add).push().regist(NODE::SUB)) | mul;
	auto ret = (BNF("return") + (*expr).push()).regist(NODE::RETURN);
	auto block = (BNF("{") + (*expr).expect(BNF(";")).push().loop() + BNF("}")).regist(NODE::BLOCK);
	auto ifExpr = ((BNF("if") + (*expr).push() + block.push()).push()[(BNF("elif") + (*expr).push() + block.push()).push().loop()][BNF("else") + block.push()]).regist(NODE::IF);
	auto whileExpr = (BNF("while") + (*expr.push()) + block.push()).regist(NODE::WHILE);
	auto structExpr = (BNF("struct")+BNF(TOKEN::IDENT).push() + BNF("{") + (type.push() + BNF(TOKEN::IDENT).push() + BNF(";")).push().loop().push() + BNF("}")).regist(NODE::STRUCT);
	expr =ret|let|whileExpr|ifExpr|assign|compare ;
	auto externFunc = (BNF("extern") + type + BNF(TOKEN::IDENT).push() + BNF("(")[type.push()[BNF(",")].loop()].push() + BNF(")") + BNF(";")).regist(NODE::EXTERN);
	auto func = (BNF("fn") + BNF(TOKEN::IDENT).push() + BNF("(")[(type.push() + BNF(TOKEN::IDENT).push())[BNF(",")].push().loop()].push() + BNF(")") + block.push()).regist(NODE::FUNCTION);
	auto program = (structExpr|externFunc | func).push().regist(NODE::BLOCK).loop();
	CodeGenerator codegen;
	codegen.emplace<ExternNode>(NODE::EXTERN);
	codegen.emplace<FunctionNode>(NODE::FUNCTION);
	codegen.emplace<CallNode>(NODE::CALL);
	codegen.emplace<RetNode>(NODE::RETURN);
	codegen.emplace<BlockNode>(NODE::BLOCK);
	codegen.emplace<DoubleNode>(NODE::FLOATING_POINT);
	codegen.emplace<IntNode>(NODE::INT);
	codegen.emplace<StructNode>(NODE::STRUCT);
	codegen.emplace<MemberNode>(NODE::MEMBER);
	codegen.emplace<ArrayAccessNode>(NODE::ARRAY_ACCESS);
	codegen.emplace<VariableNode>(NODE::VARIABLE);
	codegen.emplace<ReferenceNode>(NODE::REFERENCE);
	codegen.emplace<LetNode>(NODE::LET);
	codegen.emplace<AssignNode>(NODE::ASSIGN);
	codegen.emplace<LessNode>(NODE::LESS);
	codegen.emplace<AddNode>(NODE::ADD);
	codegen.emplace<SubNode>(NODE::SUB);
	codegen.emplace<MulNode>(NODE::MUL);
	codegen.emplace<DivNode>(NODE::DIV);
	codegen.emplace<IfNode>(NODE::IF);
	codegen.emplace<WhileNode>(NODE::WHILE);
	codegen.codegen(program(iter));
	//Generator generator;
	//generator.codegen(program(iter));
	//generator.getModule()->print(llvm::outs(),nullptr);
	codegen.getModule()->print(llvm::outs(), nullptr);
	JIT engine(codegen.getModule());
	llvm::outs()<<(int)engine.run().DoubleVal;
	llvm::outs().flush();
	return EXIT_SUCCESS;
}
//memberノードはgepを処理してloadで読み込む。パースのときにload命令をregistする
//baseCode(CodeGenerator class)
//class Generator {
//protected:
//	llvm::LLVMContext context;
//	std::unique_ptr<llvm::Module> mainModule;
//	llvm::IRBuilder<> builder;
//	std::unordered_map<std::string, llvm::AllocaInst*> variables;//variable name->{variable,valueType}
//	std::unordered_map<std::string, std::unordered_map<std::string, unsigned> > structMember;//structName->structMember->id
//	llvm::Type* retType;
//	Type typeAnalyzer;
//public:
//	Generator() :
//		mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
//		builder(context),
//		typeAnalyzer(builder)
//	{
//
//	}
//	llvm::Value* codegen(Node node) {
//		switch (node.node) {
//		case NODE::BLOCK:
//		{
//			llvm::Value* result;
//			for (const auto& child : node.branch) {
//				result = codegen(child);
//			}
//			return result;
//		}
//		break;
//		case NODE::EXTERN:
//		{
//			std::vector<llvm::Type*> args(node.branch[2].branch.size());
//			for (auto i = 0; auto & arg : args) {
//				arg = typeAnalyzer(node.branch[2].branch[i].linkBranchStr());
//				++i;
//			}
//			mainModule->getOrInsertFunction(
//				node.branch[1/*function name*/].value,//function name
//				llvm::FunctionType::get(
//					typeAnalyzer(node.branch[0].value),//return type
//					llvm::ArrayRef(args)
//					, false
//				)
//			);
//
//		}
//		break;
//		case NODE::FUNCTION:
//		{
//			std::vector<llvm::Type*> args(node.branch[1].branch.size());
//			for (auto i = 0; auto & arg : args) {
//				arg = typeAnalyzer(node.branch[1].branch[i].branch[0].linkBranchStr());
//				++i;
//			}
//			auto createFunction = [&]() {
//				variables.clear();
//				builder.SetInsertPoint(llvm::BasicBlock::Create(context, "entry",
//					llvm::Function::Create(
//						llvm::FunctionType::get(retType,//retType=builder.getVoidTy(),
//							llvm::ArrayRef(args), false),
//						llvm::Function::ExternalLinkage, node.branch[0/*function name*/].value, *mainModule)
//				));
//				for (auto i = 0; auto & arg : mainModule->getFunction(node.branch[0/*function name*/].value)->args()) {
//					variables.emplace(
//						node.branch[1].branch[i].branch[1].value,
//						builder.CreateAlloca(arg.getType(), nullptr, node.branch[1].branch[i].branch[1].value)
//					);
//					builder.CreateStore(&arg, variables[node.branch[1].branch[i].branch[1].value]);
//					++i;
//				}
//				codegen(node.branch[2/*block*/]);
//			};
//			retType = builder.getVoidTy();
//			createFunction();
//			mainModule->getFunction(node.branch[0].value)->eraseFromParent();
//			createFunction();
//		}
//		break;
//		case NODE::RETURN:
//		{
//			auto* value = codegen(node.branch[0/*expression*/]);
//			retType = value->getType();//todo:継承の度合いが一番高いのを返り値にする
//			builder.CreateRet(value);
//		}
//		break;
//		case NODE::FLOATING_POINT:
//			return llvm::ConstantFP::get(context, llvm::APFloat(std::stod(node.linkBranchStr())));
//			break;
//		case NODE::INT:
//			return llvm::ConstantInt::get(
//				context,
//				llvm::APInt(
//					std::stoi(node.branch[1].value.substr(1)),
//					std::stoi(node.branch[0].value),
//					node.branch[1].value.front() == 'u'
//				)
//			);
//			break;
//		case NODE::ADD:
//			return builder.CreateFAdd(codegen(node.branch[0]), codegen(node.branch[1]), "addtmp");
//			break;
//		case NODE::MUL:
//			return builder.CreateFMul(codegen(node.branch[0]), codegen(node.branch[1]), "multmp");
//			break;
//		case NODE::DIV:
//			return builder.CreateFDiv(codegen(node.branch[0]), codegen(node.branch[1]), "divtmp");
//			break;
//		case NODE::SUB:
//			return builder.CreateFSub(codegen(node.branch[0]), codegen(node.branch[1]), "subtmp");
//			break;
//		case NODE::ARRAY_ACCESS:
//		{
//
//			return builder.CreateLoad(
//				variables[node.branch[0].value]->getAllocatedType()->getArrayElementType(),
//				builder.CreateGEP(
//					variables[node.branch[0].value]->getAllocatedType(),
//					variables[node.branch[0].value],
//					{
//						llvm::ConstantInt::get(builder.getInt32Ty(),0),
//						codegen(node.branch[1]),
//					}
//					)
//			);
//		}
//		break;
//		case NODE::REFERENCE:
//			return variables[node.value];
//			break;
//		case NODE::VARIABLE:
//			return builder.CreateLoad(variables[node.value]->getAllocatedType(), variables[node.value]);//variables.secondType=Value*
//			break;
//		case NODE::STRUCT:
//		{
//			auto* structType = llvm::StructType::create(context, node.branch[0].value);
//			typeAnalyzer.emplace(structType->getName().str(), structType);
//			std::vector <llvm::Type* > types(node.branch[1].branch.size());
//			structMember.emplace(structType->getName().str(), decltype(structMember)::mapped_type());
//			for (unsigned i = 0; auto & type : types) {
//				type = typeAnalyzer(node.branch[1].branch[i].branch[0].linkBranchStr());
//				structMember[structType->getName().str()].emplace(node.branch[1].branch[i].branch[1].value, i);
//				++i;
//			}
//			structType->setBody(types, false);
//
//		}
//		break;
//		case NODE::MEMBER:
//			return builder.CreateLoad(
//				variables[node.branch[0].value]->getAllocatedType()->getStructElementType(structMember[node.branch[0].value][node.branch[1].value]),
//				builder.CreateStructGEP(
//					variables[node.branch[0].value]->getAllocatedType(),
//					variables[node.branch[0].value],
//					structMember[node.branch[0].value][node.branch[1].value]
//				)
//			);
//			break;
//		case NODE::ASSIGN:
//			return builder.CreateStore(
//				codegen(node.branch[1]),
//				[&]()->llvm::Value* {
//					if (node.branch[0].node == NODE::VARIABLE)return variables[node.branch[0].value];
//					else if (node.branch[0].node == NODE::MEMBER) {
//						return 	builder.CreateStructGEP(
//							variables[node.branch[0].branch[0].value]->getAllocatedType(),
//							variables[node.branch[0].branch[0].value],
//							structMember[node.branch[0].branch[0].value][node.branch[0].branch[1].value]
//						);
//					}
//					return builder.CreateGEP(
//						variables[node.branch[0].branch[0].value]->getAllocatedType(),
//						variables[node.branch[0].branch[0].value],
//						{
//							llvm::ConstantInt::get(builder.getInt32Ty(),0),
//							codegen(node.branch[0].branch[1]),
//						}
//					);
//				}()
//					);
//			break;
//		case NODE::LET:
//		{
//			if (node.branch[1].node == NODE::ARRAY) {
//				auto* value = codegen(node.branch[1].branch[0]);
//				auto* arrayValue = builder.CreateAlloca(llvm::ArrayType::get(value->getType(), node.branch[1].branch.size()));
//				for (auto i = 0; i < node.branch[1].branch.size(); ++i) {
//					builder.CreateStore(
//						codegen(node.branch[1].branch[i]),
//						builder.CreateGEP(
//							arrayValue->getAllocatedType(),
//							arrayValue,
//							{
//								llvm::ConstantInt::get(builder.getInt32Ty(),0),
//								llvm::ConstantInt::get(builder.getInt32Ty(),i),
//							}
//							)
//					);
//				}
//				variables.emplace(node.branch[0].value, arrayValue);
//				return variables[node.branch[0].value];
//			}
//			else if (node.branch[1].node == NODE::STRUCT_INIT) {
//				variables.emplace(node.branch[0].value, builder.CreateAlloca(typeAnalyzer(node.branch[1].branch[0].value)));
//				for (auto i = 0; auto & value:node.branch[1].branch[1].branch) {
//					builder.CreateStore(
//						codegen(value),
//						builder.CreateStructGEP(variables[node.branch[0].value]->getAllocatedType(), variables[node.branch[0].value], i)
//					);
//					++i;
//				}
//				return variables[node.branch[0].value];
//			}
//			auto* value = codegen(node.branch[1]);
//			variables.emplace(
//				node.branch[0].value,
//				builder.CreateAlloca(value->getType(), nullptr, node.branch[0].value)
//			);
//			return builder.CreateStore(value, variables[node.branch[0].value]);
//		}
//		break;
//		case NODE::LESS:
//			return builder.CreateUIToFP(builder.CreateFCmpULT(codegen(node.branch[0]), codegen(node.branch[1]), "compareTemp"), builder.getDoubleTy(), "boolTemp");
//			break;
//		case NODE::IF:
//		{
//			std::vector<llvm::BasicBlock*> blocks;
//			for (auto i = 0; i <= node.branch.size(); ++i) {
//				blocks.push_back(llvm::BasicBlock::Create(context, "ifBlock", builder.GetInsertBlock()->getParent()));
//			}
//			llvm::BasicBlock* before;
//			for (auto i = 0; i < blocks.size() - 1 - (node.branch[node.branch.size() - 1].branch.size() == 1); ++i) {
//				before = node.branch.size() == 1 ? blocks.back() : llvm::BasicBlock::Create(context, "branch", builder.GetInsertBlock()->getParent());
//				builder.CreateCondBr(
//					builder.CreateFCmpONE(codegen(node.branch[i].branch[0]), llvm::ConstantFP::get(context, llvm::APFloat(0.0)), "ifcond"),
//					blocks[i],
//					before
//				);
//				builder.SetInsertPoint(before);
//			}
//			if (node.branch[node.branch.size() - 1].branch.size() == 1) {
//				builder.CreateBr(blocks[blocks.size() - 2]);
//			}
//			for (auto i = 0; i < blocks.size() - 1 - (node.branch[node.branch.size() - 1].branch.size() == 1); ++i) {
//				builder.SetInsertPoint(blocks[i]);
//				codegen(node.branch[i].branch[1]);
//				builder.CreateBr(blocks.back());
//			}
//			if (node.branch[node.branch.size() - 1].branch.size() == 1) {
//				builder.SetInsertPoint(blocks[blocks.size() - 2]);
//				codegen(node.branch[node.branch.size() - 1]);
//				builder.CreateBr(blocks.back());
//			}
//
//			builder.SetInsertPoint(blocks.back());
//		}
//		break;
//		case NODE::WHILE:
//		{
//			auto* function = builder.GetInsertBlock()->getParent();
//			auto* loop = llvm::BasicBlock::Create(context, "loop", function);
//			auto* then = llvm::BasicBlock::Create(context, "then", function);
//			auto* after = llvm::BasicBlock::Create(context, "afterLoop", function);
//			builder.CreateBr(loop);
//			builder.SetInsertPoint(loop);
//			builder.CreateCondBr(
//				builder.CreateFCmpONE(codegen(node.branch[0]), llvm::ConstantFP::get(context, llvm::APFloat(0.0)), "loopCond"),
//				then,
//				after
//			);
//			builder.SetInsertPoint(then);
//			codegen(node.branch[1]);
//			builder.CreateBr(loop);
//			builder.SetInsertPoint(after);
//		}
//		break;
//		case NODE::CALL:
//		{
//			std::vector<llvm::Value*> args(node.branch[1].branch.size());
//			for (auto i = 0; auto & arg:args) {
//				arg = codegen(node.branch[1].branch[i]);
//			}
//			return builder.CreateCall(mainModule->getFunction(node.branch[0].value), args);
//		}
//		break;
//		}
//	}
//	auto& getModule() {
//		return mainModule;
//	}
//};