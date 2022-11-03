#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/IR/IRBuilder.h"    
#include "llvm/IR/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/TargetSelect.h"
#include <fstream>
#include <stack>
#include <memory>
#include <string>
#include <sstream>
#include <functional>
#include <iostream>
#include <regex>
#include <unordered_map>
class File {
private:
	const std::string name;
public:
	File(decltype(name) nmae):name(name) {
	}
	std::string read() {
		std::fstream file(name);
		if (!file)return "";
		return std::string(std::istreambuf_iterator<char>(file), std::istreambuf_iterator<char>());
	}
};
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
	ARRAY_ACCESS_LOAD,
	SCALAR,
	REFERENCE,
	STRUCT,
	STRUCT_INIT,
	MEMBER,
	MEMBER_LOAD,
	STRING
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
	std::unordered_map<std::string, llvm::Value*> variables;
	std::unordered_map<std::string, std::unordered_map<std::string, unsigned> > structMember;
public:
	CodeGenerator() :
		mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
		builder(context),
		typeAnalyzer(builder)
	{
		context.setOpaquePointers(false);
	}
	auto& getStructMember() {
		return structMember;
	}
	auto& getVariables() {
		return variables;
	}
	auto &getType() {
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
class  TypeIdentNode{
private:
public:
	enum BRANCH {
		TYPE,
		NAME
	};
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
class StringNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg,Node node)override {
		return cg.getBuilder().CreateGlobalStringPtr(node.value.substr(1,node.value.size()-2));
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

class ArrayAccessLoadNode :public Codegen{
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables()[node.branch[0].branch[0].value]->getType()->getNonOpaquePointerElementType()->getArrayElementType(),
			cg.codegen(node)
		);
	}
};

class ArrayAccessNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateGEP(
				cg.getVariables()[node.branch[0].value]->getType()->getNonOpaquePointerElementType(),
				cg.getVariables()[node.branch[0].value],
				{
					llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
					cg.codegen(node.branch[1]),
				}

		);
	}
};
class VariableNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables()[node.value]->getType()->getNonOpaquePointerElementType(),
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
class StructInitNode :public Codegen{
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {//idea:structName{membername:value,membername2:value2};
		auto* structValue = cg.getBuilder().CreateAlloca(cg.getType()(node.branch[0].value));
		for (auto i = 0; auto & value:node.branch[1].branch) {
			cg.getBuilder().CreateStore(
				cg.codegen(value),
				cg.getBuilder().CreateStructGEP(structValue->getAllocatedType(), structValue, i)
			);
			++i;
		}
		return structValue;
	}
};
class ArrayNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* arrayValue = cg.getBuilder().CreateAlloca(llvm::ArrayType::get(cg.codegen(node.branch[0])->getType(), node.branch.size()));
		for (auto i = 0; i < node.branch.size(); ++i) {
			cg.getBuilder().CreateStore(
				cg.codegen(node.branch[i]),
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
		return arrayValue;
	}
};
class ScalarNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* value = cg.codegen(node.branch[0]);
		auto*variable=cg.getBuilder().CreateAlloca(value->getType());
		cg.getBuilder().CreateStore(value, variable);
		return variable;
	}
};
class LetNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		cg.getVariables().emplace(node.branch[0].value,cg.codegen(node.branch[1]));
		cg.getVariables()[node.branch[0].value]->setName(node.branch[0].value);
		return cg.getVariables()[node.branch[0].value];
	}
};

class AssignNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateStore(
			cg.codegen(node.branch[1]),
			cg.codegen(node.branch[0])
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
	//enum class//need cast
	enum BRANCH {
		NAME,
		ARGUMENTS
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Type*> args(node.branch[ARGUMENTS].branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = cg.getType()(node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::TYPE].linkBranchStr());
			++i;
		}
		auto createFunction = [&]() {
			cg.getVariables().clear();
			cg.getBuilder().SetInsertPoint(llvm::BasicBlock::Create(cg.getBuilder().getContext(), "entry",
				llvm::Function::Create(
					llvm::FunctionType::get(cg.getRetType(),//retType=builder.getVoidTy(),
						llvm::ArrayRef(args), false),
					llvm::Function::ExternalLinkage, node.branch[NAME].value, *cg.getModule())
			));
			for (auto i = 0; auto & arg : cg.getModule()->getFunction(node.branch[NAME].value)->args()) {
				if(arg.getType()->isPointerTy()){
					cg.getVariables().emplace(
						node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value,
						&arg
					);
				}
				else {
					cg.getVariables().emplace(
						node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value,
						cg.getBuilder().CreateAlloca(arg.getType(), nullptr, node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value)
					);
					cg.getBuilder().CreateStore(&arg, cg.getVariables()[node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value]);
				}
				++i;
			}
			cg.codegen(node.branch[2/*block*/]);
		};
		cg.getRetType() = cg.getBuilder().getVoidTy();
		createFunction();
		cg.getModule()->getFunction(node.branch[NAME].value)->eraseFromParent();
		createFunction();
		return cg.getModule()->getFunction(node.branch[NAME].value);
	}
};
class CallNode :public Codegen {
private:
public:
	enum BRANCH {//functionと同じだが、functionNodeの定義が変わるとバグになりかねないので別の物として定義する
		NAME,
		ARGUMENTS
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Value*> args(node.branch[ARGUMENTS].branch.size());
		for (auto i = 0; auto & arg:args) {
			arg = cg.codegen(node.branch[ARGUMENTS].branch[i]);
			++i;
		}
		return cg.getBuilder().CreateCall(cg.getModule()->getFunction(node.branch[NAME].value), args);
	}
};
class MemberNode :public Codegen {
private:
public:
	enum BRANCH {
		OBJ,
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		//llvm::Value* value = cg.getVariables()[node.branch[OBJ_NAME].value];
		auto getRawRetType = [&cg](std::string name) {
			if (cg.getModule()->getFunction(name)->getReturnType()->isPointerTy()) {
				return cg.getModule()->getFunction(name)->getReturnType()->getNonOpaquePointerElementType();
			}
			return cg.getModule()->getFunction(name)->getReturnType();
		};
		auto type = [&]() {
			if (node.branch.front().node==NODE::REFERENCE) {
				return cg.getVariables()[node.branch.front().value]->getType()->getNonOpaquePointerElementType();
			}
			return getRawRetType(node.branch.front().branch[CallNode::NAME].value);
		}();
		auto iter = node.branch.begin();
		for (auto member = node.branch.begin(); member!= node.branch.end(); ++member) {
			if (member->node != NODE::CALL)continue;
			member->branch[CallNode::NAME].value.insert(
				0,
				type->getStructName().str()+"_"
			);
			Node self;
			if (std::distance(iter,member)==1) {
				self = *iter;
			}
			else {
				self.node = NODE::MEMBER;
				self.branch.insert(
					self.branch.begin(),
					iter,
					member
				);
			}
			member->branch[CallNode::ARGUMENTS].branch.insert(
				member->branch[CallNode::ARGUMENTS].branch.begin(),
				self
			);
			iter = member;
			type = getRawRetType(member->branch[CallNode::NAME].value);
		}
		node.branch.erase(node.branch.begin(),iter);
		auto value = cg.codegen(node.branch.front());
		std::for_each(++node.branch.begin(),node.branch.end(),
			[
				&
			](auto &member)mutable{
				value = cg.getBuilder().CreateStructGEP(
					value->getType()->getNonOpaquePointerElementType(),
					value,
					cg.getStructMember()[value->getType()->getNonOpaquePointerElementType()->getStructName().str()][member.value]
				);
			});
		return value;
	}
};

class MemberLoadNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		constexpr auto memberNode = 0;
		auto member = cg.codegen(node.branch[memberNode]);
		//if (node.branch[memberNode].branch[MemberNode::MEMBER].branch.back().node==NODE::CALL) {
		if (node.branch[memberNode].branch.back().node == NODE::CALL) {
			return member;
		}
		return cg.getBuilder().CreateLoad(member->getType()->getNonOpaquePointerElementType(), member);
	}
};
class StructNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		constexpr auto STRUCT_MEMBERS = 1;
		auto* structType = llvm::StructType::create(cg.getBuilder().getContext(), node.branch[0].value);
		cg.getType().emplace(structType->getName().str(), structType);
		std::vector <llvm::Type* > types;
		cg.getStructMember().emplace(structType->getName().str(), std::unordered_map<std::string, unsigned>{});
		for (unsigned hash = 0; auto & member : node.branch[STRUCT_MEMBERS].branch) {
			if (member.node != NODE::FUNCTION) {
				types.push_back(cg.getType()(member.branch[TypeIdentNode::TYPE].linkBranchStr()));
				cg.getStructMember()[structType->getName().str()].emplace(member.branch[TypeIdentNode::NAME].value, hash);
				++hash;
			}
		}
		structType->setBody(types, false);
		for (auto& member : node.branch[STRUCT_MEMBERS].branch) {
			if (member.node != NODE::FUNCTION)continue;
			member.branch[FunctionNode::NAME].value.insert(
				0,
				structType->getName().str() + "_"
			);
			Node self;
			self.branch.resize(2/*TypeIdentNode branch max size*/);
			self.branch.front().branch.resize(1);
			self.branch.front().branch.front().value = structType->getName().str() + "*";
			self.branch[TypeIdentNode::NAME].value = "this";
			member.branch[FunctionNode::ARGUMENTS].branch.emplace(//push_back is ok
				member.branch[FunctionNode::ARGUMENTS].branch.begin(),
				self
			);
			cg.codegen(member);
		}
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
				, node.branch.size()==4
			)
		);
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
int main(int args, char* argv[]) {
	auto tokens = Lexer().tokenize("extern i32 puts(i32*);fn main(){let str=\"string\";puts(str);return {1.0;};}");
	auto iter = tokens.begin();
	auto number = BNF(TOKEN::NUMBER).regist(NODE::NUMBER);
	auto string = BNF(TOKEN::STRING).regist(NODE::STRING);
	auto type = BNF(TOKEN::IDENT).push()[BNF("*").push().loop()];
	auto variable = BNF(TOKEN::IDENT).regist(NODE::VARIABLE);
	auto reference = (BNF("&") + variable).regist(NODE::REFERENCE);
	auto floatNum = (number.push() + BNF(".").push() + number.push()).regist(NODE::FLOATING_POINT);//.number|f
	auto intNum = (number.push() + BNF(TOKEN::IDENT).push()).regist(NODE::INT);
	BNF expr;
	auto call = (BNF(TOKEN::IDENT).push() + BNF("(")[(*expr).push()[BNF(",")].loop()].push() + BNF(")")).regist(NODE::CALL);
	auto arrayAccess = (variable.push() + BNF("[") + (*expr).push() + BNF("]")).regist(NODE::ARRAY_ACCESS);
	auto member = ((call | variable.regist(NODE::REFERENCE)).push() + ((BNF(".") + (call | variable.regist(NODE::REFERENCE))).push().loop())).regist(NODE::MEMBER);
	auto arrayExpr = (BNF("[") + ((*expr).push()[BNF(",")]).loop() + BNF("]")).regist(NODE::ARRAY);
	auto structInit = (BNF(TOKEN::IDENT).push() + BNF("{") + ((*expr).push()[BNF(",")]).loop().push() + BNF("}")).regist(NODE::STRUCT_INIT);//ident(member)+expr
	BNF  add;
	auto compare = ((*add).push() + BNF("<") + (*add).push()).regist(NODE::LESS) | (*add);	
	//auto let=BNF("let")+assign;alloca->assignCodeGen
	auto let = (BNF("let") + BNF(TOKEN::IDENT).push() + BNF("=") + (arrayExpr|structInit|(*expr).push().regist(NODE::SCALAR)).push()).regist(NODE::LET);
	auto assign = ((arrayAccess|member|variable.regist(NODE::REFERENCE)).push() + BNF("=") + (*expr).push()).regist(NODE::ASSIGN);
	auto primary = BNF("(")+(*compare).expect(BNF(")")) | intNum|floatNum| structInit|arrayExpr|arrayAccess.push().regist(NODE::ARRAY_ACCESS_LOAD) | member.push().regist(NODE::MEMBER_LOAD) | call | reference | variable|string;
	auto mul = (primary.push()+(BNF("*") + (*primary).push()).regist(NODE::MUL) | BNF("/") + (*primary).push().regist(NODE::DIV)) | primary;
	add =( mul.push() + (BNF("+") + (*add).push()).regist(NODE::ADD) | BNF("-") + (*add).push().regist(NODE::SUB)) | mul;
	auto ret = (BNF("return") + (*expr).push()).regist(NODE::RETURN);
	auto block = (BNF("{") + (*expr).expect(BNF(";")).push().loop() + BNF("}")).regist(NODE::BLOCK);
	auto ifExpr = ((BNF("if")[BNF("(")] + (*expr).push()[BNF(")")] + block.push()).push()[((BNF("elif") | BNF("else") + BNF("if"))[BNF("(")] + (*expr).push()[BNF(")")] + block.push()).push().loop()][BNF("else") + block.push()]).regist(NODE::IF);
	auto whileExpr = (BNF("while")[BNF("(")] + (*expr.push())[BNF(")")] + block.push()).regist(NODE::WHILE);
	expr =ret|let|whileExpr|ifExpr|assign|compare|block ;
	auto externFunc = (BNF("extern") + type + BNF(TOKEN::IDENT).push() + BNF("(")[(type).push()[BNF(",")].loop()].push()[(BNF(".")+BNF(".")+BNF(".")).push()] + BNF(")") + BNF(";")).regist(NODE::EXTERN);
	auto function = (BNF("fn") + BNF(TOKEN::IDENT).push() + BNF("(")[(type.push() + BNF(TOKEN::IDENT).push())[BNF(",")].push().loop()].push() + BNF(")") + block.push()).regist(NODE::FUNCTION);
	auto structExpr = (BNF("struct") + BNF(TOKEN::IDENT).push() + BNF("{") + ((type.push() + BNF(TOKEN::IDENT).push() + BNF(";")) | function).push().loop().push() + BNF("}")).regist(NODE::STRUCT);
	auto program = (structExpr|externFunc | function).push().regist(NODE::BLOCK).loop();
	CodeGenerator codegen;
	codegen.emplace<ExternNode>(NODE::EXTERN);
	codegen.emplace<FunctionNode>(NODE::FUNCTION);
	codegen.emplace<CallNode>(NODE::CALL);
	codegen.emplace<RetNode>(NODE::RETURN);
	codegen.emplace<BlockNode>(NODE::BLOCK);
	codegen.emplace<StringNode>(NODE::STRING);
	codegen.emplace<DoubleNode>(NODE::FLOATING_POINT);
	codegen.emplace<IntNode>(NODE::INT);
	codegen.emplace<StructNode>(NODE::STRUCT);
	codegen.emplace<StructInitNode>(NODE::STRUCT_INIT);
	codegen.emplace<MemberNode>(NODE::MEMBER);
	codegen.emplace<ArrayNode>(NODE::ARRAY);
	codegen.emplace<ArrayAccessNode>(NODE::ARRAY_ACCESS);
	codegen.emplace<ScalarNode>(NODE::SCALAR);
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
	codegen.emplace<ArrayAccessLoadNode>(NODE::ARRAY_ACCESS_LOAD);
	codegen.emplace<MemberLoadNode>(NODE::MEMBER_LOAD);
	codegen.codegen(program(iter));
	codegen.getModule()->print(llvm::outs(), nullptr);
	JIT engine(codegen.getModule());
	llvm::outs() << engine.run().IntVal<<"\n";
	llvm::outs()<<(int)engine.run().DoubleVal;
	llvm::outs().flush();
	return EXIT_SUCCESS;
}