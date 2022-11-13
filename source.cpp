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
#include <queue>
#include <memory>
#include <string>
#include <sstream>
#include <functional>
#include <stack>
#include <iostream>
#include <iterator>
#include <regex>
#include <array>
#include <unordered_map>
inline constexpr auto makeArray(auto&&... args) {
	return std::move(std::array< decltype(std::initializer_list{ args... })::value_type, sizeof...(args) > {args...});
}
class File {
private:
	const std::string name;
public:
	File(decltype(name) name) :name(name) {
	}
	std::string read() {
		std::fstream file(name);
		if (!file) return "";
		return std::string(std::istreambuf_iterator<decltype(name)::value_type >(file), std::istreambuf_iterator<decltype(name)::value_type>());
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
		str.push_back('\n');
		str = std::regex_replace(str, std::regex(R"((//.*?[^\n]\n)|[\n])"), "");
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
				check(TOKEN::RESERVED, R"(^[&\[\];:,\.\(\)+*/=\-<>{}])") ||
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
	STRING,
	CLASS,
	MEMBER_REGIST,
	CLASS_ACCESS,
	CONSTRUCTOR,
	DEFINE
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
		return BNF([parser = this->parser, value = std::move(node)](Iter iter) {
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
			std::queue<unsigned> arraySizes;
			for (auto pos = str.find_last_of('['); pos != std::string::npos; str.erase(pos), pos = str.find_last_of('[')) {
				arraySizes.push(std::stoi(str.substr(pos + 1, str.size() - 3)));//
			}
			auto type = [&]()->llvm::Type* {
				if (types.count(str)) {
					return types[str];
				}
				else if (str.front() == 'i') {
					return builder.getIntNTy(std::stoi(str.substr(1)));
				}
				return builder.getVoidTy();
			}();
			while (!arraySizes.empty()) {
				type = llvm::ArrayType::get(type, arraySizes.front());
				arraySizes.pop();
			}
			for (auto i = 0; i < pointer; ++i) {
				type = type->getPointerTo();
			}
			return type;
		};
	}
	auto emplace(decltype(types)::key_type key, decltype(types)::mapped_type value) {//todo:use this. using statement
		types.emplace(key, value);
	}
	auto erase(decltype(types)::key_type &&key) {
		types.erase(std::forward<decltype(types)::key_type>(key));
	}
	auto operator()(const std::string str) {
		return analyze(std::move(str));
	}
};
class Variables {
private:
	bool saveMode=true;
	unsigned id = 0;
	std::unordered_map<unsigned, unsigned> counter;
	//std::vector<int> idCount;
	//std::unordered_map<llvm::Value*, unsigned> a;
	//std::unordered_map<std::string, unsigned> counter;
	std::vector < std::unordered_map < std::string, std::pair<llvm::Value*,unsigned> > > variables;
	std::function<void(std::string,llvm::Value*)> callback;
public:
	template <class T>
	auto changeCallback(T callback) {
		this->callback=std::move(callback);
	}
	auto setMode(decltype(saveMode) mode) {
		id = 0;
		saveMode = mode;
	}
	auto nest() {
		variables.push_back({});
	}
	template <class keyT,class valueT>
	auto insert_or_assign(keyT&& key, valueT&& value) {
		variables.back().insert_or_assign(std::forward<keyT>(key),std::make_pair(std::forward<valueT>(value),id));
		counter.emplace(id,0);
		++id;
	}
	auto& get(decltype(variables)::value_type::key_type name) {
		for (auto i = variables.rbegin(); i != variables.rend(); ++i) {
			if (!i->count(name))continue;
			if (saveMode) {
				++counter.at(i->at(name).second);			
			}
			else if (counter.count(i->at(name).second) && --counter.at(i->at(name).second) == 0) {
			    callback(name, i->at(name).first);
				counter.erase(i->at(name).second);
			}
			return i->at(name).first;
		}
	}
	auto exitScope() {
		auto variables = std::move(this->variables.back());
		this->variables.pop_back();
		return std::move(variables);
	}
};
enum class ACCESS {
	PUBLIC,
	PRIVATE,
	PROTECTED
};
class MemberInfo {
private:
	const ACCESS access;
	const unsigned offset;
public:
	MemberInfo(decltype(access) access, decltype(offset) offset) :access(access), offset(offset) {}
	const auto& getOffset() const {
		return offset;
	}
	const auto& getAccess()const{
		return access;
	}
};
class Member {
private:
	std::unordered_map<std::string, MemberInfo > member;//member->access,offset
public:
	auto emplace(decltype(member)::key_type key, ACCESS access) {
		member.emplace(std::piecewise_construct, std::forward_as_tuple(std::move(key)), std::forward_as_tuple(access, member.size()));
	}
	const auto& get(decltype(member)::key_type key)const{
		return member.at(std::move(key));
	}
};
class Classes {
private:

	std::unordered_map<std::string, Member> classes;
public:
	auto emplace(decltype(classes)::key_type className,std::string memberName,ACCESS access) {
		classes[std::move(className)].emplace(std::move(memberName), access);
	}
	const auto &getMember(std::string from, decltype(classes)::key_type className, std::string memberName)const{//一時的な物
		return classes.at(std::move(className)).get(std::move(memberName));
	}
	bool is_class(decltype(classes)::key_type key) {
		return classes.count(std::move(key));
	}
};
class CodeGenerator;
class Codegen {
private:
public:
	virtual llvm::Value* codegen(CodeGenerator&, Node) = 0;
};
class CodeGenerator {
private:
	std::unordered_map<NODE, std::unique_ptr<Codegen> > generators;
	llvm::LLVMContext context;
	std::unique_ptr<llvm::Module> mainModule;
	llvm::IRBuilder<> builder;
	Type typeAnalyzer;
	llvm::Type* retType;
	llvm::BasicBlock* retBlock;
	Variables variables;
	Classes classes;
	std::stack<std::function<void()>> tasks;
	std::unordered_map<std::string, std::unordered_map<std::string, unsigned> > structMember;
public:
	CodeGenerator() :
		mainModule(std::make_unique<decltype(mainModule)::element_type>("module", context)),
		builder(context),
		typeAnalyzer(builder)
	{
		context.setOpaquePointers(false);
	}
	template <class T>
	auto setDestructorCallback(T&& callback) {
		variables.changeCallback(std::forward<T>(callback));
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
	auto& getRetBlock() {
		return retBlock;
	}
	auto& getModule() {
		return mainModule;
	}
	auto& getClasses() {
		return classes;
	}
	template <class T, class... ArgT>
	auto emplace(decltype(generators)::key_type key, ArgT... args) {
		generators.emplace(key, std::make_unique<T>(args...));
	}
	auto& getBuilder() {
		return builder;
	}
	auto registTask(auto task) {
		tasks.push(task);
	}
	llvm::Value* codegen(Node node) {
		while (!tasks.empty()) {
			tasks.top()();
			tasks.pop();
		}
		return generators[node.node]->codegen(*this, node);
	}
};
class NoneNode :public Codegen {
public:
	llvm::Value* codegen(CodeGenerator&, Node)override {
		return nullptr;
	}
}; 
class  TypeIdentNode {
private:
public:
	enum BRANCH {
		TYPE,
		NAME
	};
};
class AddNode :public Codegen {
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
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
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateGlobalStringPtr(node.value.substr(1, node.value.size() - 2));
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

class ArrayAccessLoadNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto arrayValue = cg.codegen(node.branch[0]);
		return cg.getBuilder().CreateLoad(
			arrayValue->getType()->getNonOpaquePointerElementType(),
			arrayValue
		);
	}
};

class ArrayAccessNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto arrayRef = cg.codegen(node.branch[0]);
		for (auto& index : node.branch[1].branch) {
			arrayRef = cg.getBuilder().CreateGEP(
				arrayRef->getType()->getNonOpaquePointerElementType(),
				arrayRef,
				{
					llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
					cg.codegen(index),
				}
			);
		}
		return arrayRef;
	}
};
class VariableNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateLoad(
			cg.getVariables().get(node.value)->getType()->getNonOpaquePointerElementType(),
			cg.getVariables().get(node.value)
		);
	}
};
class ReferenceNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getVariables().get(node.value);
	}
};
class StructInitNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* structValue = cg.getBuilder().CreateAlloca(cg.getType()(node.branch[0].value));
		for (auto& value : node.branch[1].branch) {
			cg.getBuilder().CreateStore(
				cg.codegen(value.branch[1]),
				cg.getBuilder().CreateStructGEP(
					structValue->getAllocatedType(),
					structValue,
					cg.getStructMember()[structValue->getAllocatedType()->getStructName().str()][value.branch[0].value]
				)
			);
		}
		return structValue;
	}
};
class ArrayNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto createType = [&](auto& self, auto& node) {
			if (node.branch[0].node != NODE::ARRAY) {
				return llvm::ArrayType::get(cg.codegen(node.branch[0])->getType(), node.branch.size());
			}
			return llvm::ArrayType::get(self(self, node.branch[0]), node.branch.size());
		};
		auto arrayValue = cg.getBuilder().CreateAlloca(createType(createType, node));
		auto store = [&](auto& self, auto& node, auto arrayValue)->void {
			for (auto i = 0; i < node.branch.size(); ++i) {
				if (node.branch[i].node == NODE::ARRAY) {
					self(
						self,
						node.branch[i],
						cg.getBuilder().CreateGEP(
							arrayValue->getType()->getNonOpaquePointerElementType(),
							arrayValue,
							{
								llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
								llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),i),
							}
							)
					);
					continue;
				}
				cg.getBuilder().CreateStore(
					cg.codegen(node.branch[i]),
					cg.getBuilder().CreateGEP(
						arrayValue->getType()->getNonOpaquePointerElementType(),
						arrayValue,
						{
							llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),0),
							llvm::ConstantInt::get(cg.getBuilder().getInt32Ty(),i),
						}
						)
				);
			}
		};
		store(store, node, arrayValue);
		return arrayValue;
	}
};
class ScalarNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* value = cg.codegen(node.branch[0]);
		if (value->getType()->isPointerTy())return value;
		auto* variable = cg.getBuilder().CreateAlloca(value->getType());
		cg.getBuilder().CreateStore(value, variable);
		return variable;
	}
};
class LetNode :public Codegen {
private:
public:
	enum BRANCH {
		NAME,
		VALUE
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		cg.getVariables().insert_or_assign(node.branch[NAME].value, cg.codegen(node.branch[VALUE]));
		return cg.getVariables().get(node.branch[NAME].value);
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
		cg.getVariables().nest();
		llvm::Value* result;
		for (const auto& child : node.branch) {
			result = cg.codegen(child);
		}
		cg.getVariables().exitScope();
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
class RetNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		llvm::Value* value = nullptr;
		if (!node.branch.empty()) {
			value = cg.codegen(node.branch[0/*expression*/]);
			cg.getRetType() = value->getType();
			cg.getBuilder().CreateStore(value, cg.getVariables().get("return"));
		}
		cg.getBuilder().CreateBr(cg.getRetBlock());
		//afterは一つだけでもいい
		cg.getBuilder().SetInsertPoint(llvm::BasicBlock::Create(cg.getBuilder().getContext(),"after",cg.getBuilder().GetInsertBlock()->getParent()));
		return value;
	}
};
class FunctionNode :public Codegen {
private:
public:
	enum BRANCH {
		NAME,
		ARGUMENTS,
		TYPE,
		BLOCK
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		std::vector<llvm::Type*> args(node.branch[ARGUMENTS].branch.size());
		for (auto i = 0; auto & arg : args) {
			arg = cg.getType()(node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::TYPE].linkBranchStr());
			++i;
		}
		auto createFunction = [&]() {
			cg.getBuilder().SetInsertPoint(llvm::BasicBlock::Create(cg.getBuilder().getContext(), "entry",
				llvm::Function::Create(
					llvm::FunctionType::get(cg.getRetType(),
						llvm::ArrayRef(args), false),
					llvm::Function::ExternalLinkage, node.branch[NAME].value, *cg.getModule())
			));
			for (auto i = 0; auto & arg : cg.getModule()->getFunction(node.branch[NAME].value)->args()) {
				if (arg.getType()->isPointerTy()) {
					cg.getVariables().insert_or_assign(
						node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value,
						&arg
					);
				}
				else {
					cg.getVariables().insert_or_assign(
						node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value,
						cg.getBuilder().CreateAlloca(arg.getType(), nullptr, node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value)
					);
					cg.getBuilder().CreateStore(&arg, cg.getVariables().get(node.branch[ARGUMENTS].branch[i].branch[TypeIdentNode::NAME].value));
				}
				++i;
			}
			cg.getRetBlock() = llvm::BasicBlock::Create(cg.getBuilder().getContext(),"return", cg.getBuilder().GetInsertBlock()->getParent());
			cg.getVariables().nest();
			cg.getVariables().insert_or_assign("return",cg.getRetType()==cg.getBuilder().getVoidTy() ? nullptr:cg.getBuilder().CreateAlloca(cg.getRetType()));
			cg.codegen(node.branch[BLOCK]);
			cg.getBuilder().SetInsertPoint(cg.getRetBlock());
			Node node;
			node.node = NODE::VARIABLE;
			node.value = "return";
			cg.getBuilder().CreateRet(cg.getVariables().get("return") ? cg.codegen(node):nullptr);
			cg.getVariables().exitScope();
		};
		if (node.branch[TYPE].branch.size()) {
			cg.getRetType() = cg.getType()(node.branch[TYPE].linkBranchStr());
			cg.getVariables().setMode(true);
			createFunction();
			cg.getModule()->getFunction(node.branch[NAME].value)->eraseFromParent();
			cg.getVariables().setMode(false);
			createFunction();
		}
		else {
			cg.getRetType() = cg.getBuilder().getVoidTy();
			cg.getVariables().setMode(true);
			createFunction();
			cg.getModule()->getFunction(node.branch[NAME].value)->eraseFromParent();
			cg.getVariables().setMode(false);
			createFunction();

		}
		return cg.getModule()->getFunction(node.branch[NAME].value);
	}
};
//operator()
class CallNode :public Codegen {
private:
public:
	enum BRANCH {
		NAME,
		ARGUMENTS
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		if (cg.getClasses().is_class(node.branch[NAME].value)) {
			node.node = NODE::CONSTRUCTOR;
			return cg.codegen(node);
		}
		std::vector<llvm::Value*> args(node.branch[ARGUMENTS].branch.size());
		for (auto i = 0; auto & arg:args) {
			arg = cg.codegen(node.branch[ARGUMENTS].branch[i]);
			++i;
		}
		return cg.getBuilder().CreateCall(cg.getModule()->getFunction(node.branch[NAME].value), args);
	}
};
class DefineNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		return cg.getBuilder().CreateAlloca(cg.getType()(node.linkBranchStr()));
	}
};
class ConstructorNode :public Codegen {
private:
public:
	llvm::Value* codegen(CodeGenerator& cg,Node node)override {
		constexpr auto WORK_SPACE = "0";
		cg.getVariables().nest();
		cg.getVariables().insert_or_assign(WORK_SPACE, cg.getBuilder().CreateAlloca(cg.getType()(node.branch[CallNode::NAME].value)));
		node.branch[CallNode::ARGUMENTS].branch.insert(
			node.branch[CallNode::ARGUMENTS].branch.begin(),
			Node()
		);
		node.branch[CallNode::ARGUMENTS].branch.front().value = WORK_SPACE;
		node.branch[CallNode::ARGUMENTS].branch.front().node = NODE::REFERENCE;
		node.branch[CallNode::NAME].value += "_constructor";
		node.node = NODE::CALL;
		cg.codegen(node);
		return cg.getVariables().exitScope().at(WORK_SPACE).first;
	}
};
class MemberNode :public Codegen {
private:
public:
	enum BRANCH {
		OBJ,
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto getRawRetType = [&cg](std::string &name) {
			if (cg.getClasses().is_class(name))return cg.getType()(name);
			if (cg.getModule()->getFunction(name)->getReturnType()->isPointerTy()) {
				return cg.getModule()->getFunction(name)->getReturnType()->getNonOpaquePointerElementType();
			}
			return cg.getModule()->getFunction(name)->getReturnType();
		};
		auto type = [&]() {
			if (node.branch.front().node == NODE::REFERENCE) {
				return cg.getVariables().get(node.branch.front().value)->getType()->getNonOpaquePointerElementType();
			}
			return getRawRetType(node.branch.front().branch[CallNode::NAME].value);
		}();
		auto iter = node.branch.begin();
		for (auto member = node.branch.begin(); member != node.branch.end(); ++member) {
			if (member->node != NODE::CALL)continue;
			if (!cg.getClasses().is_class(member->branch[CallNode::NAME].value)&&!cg.getModule()->getFunction(member->branch[CallNode::NAME].value)) {
				member->branch[CallNode::NAME].value.insert(
					0,
					type->getStructName().str() + "_"
				);
			}
			Node self;
			if (std::distance(iter, member) == 1) {
				self = *iter;
			}
			else{
				self.node = NODE::MEMBER;
				self.branch.insert(
					self.branch.begin(),
					iter,
					member
				);
			}
			if (std::distance(iter, member)) {
				member->branch[CallNode::ARGUMENTS].branch.insert(
					member->branch[CallNode::ARGUMENTS].branch.begin(),
					self
				);
			}
			iter = member;
			type = getRawRetType(member->branch[CallNode::NAME].value);
		}
		node.branch.erase(node.branch.begin(), iter);
		auto value = cg.codegen(node.branch.front());
		std::for_each(++node.branch.begin(), node.branch.end(),
			[
				&
			](auto& member)mutable {
				value = cg.getBuilder().CreateStructGEP(
					value->getType()->getNonOpaquePointerElementType(),
					value,
					[&] {
						const auto name= value->getType()->getNonOpaquePointerElementType()->getStructName().str();
						if (cg.getStructMember().count(name)) {
							return cg.getStructMember()[name][member.value];
						}
						const auto obj=cg.getClasses().getMember("", name, member.value);
						const auto parentName = std::move(cg.getBuilder().GetInsertBlock()->getParent()->getName().str());
						if (
							obj.getAccess()
							==
							ACCESS::PRIVATE&&
							!std::equal(parentName.begin(),std::next(parentName.begin(),name.size()),name.begin(),name.end() )
							)
						{
							throw "private member";
						}
						return obj.getOffset();
					}()
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
		if (node.branch[memberNode].branch.back().node == NODE::CALL) {
			return member;
		}
		return cg.getBuilder().CreateLoad(member->getType()->getNonOpaquePointerElementType(), member);
	}
};
class ClassNode :public Codegen {
private:
public:
	enum BRANCH {
		NAME,
		MEMBERS
	};
	llvm::Value* codegen(CodeGenerator &cg, Node node)override {
		auto* structType = llvm::StructType::create(cg.getBuilder().getContext(), node.branch[NAME].value);
		std::vector <llvm::Type* > types;
		cg.getType().emplace(structType->getName().str(), structType);
		for (ACCESS access; auto & member : node.branch[MEMBERS].branch) {
			if (member.node == NODE::CLASS_ACCESS) {
				access=std::unordered_map<decltype(member.value), ACCESS>{
					{"public", ACCESS::PUBLIC},
					{ "private",ACCESS::PRIVATE },
					{ "protected",ACCESS::PROTECTED },
				}.at(member.branch.front().value);
				continue;
			}
			if (member.node != NODE::MEMBER_REGIST) {
				continue;
			}
			types.push_back(cg.getType()(member.branch[TypeIdentNode::TYPE].linkBranchStr()));
			cg.getClasses().emplace(node.branch[NAME].value, member.branch[TypeIdentNode::NAME].value,access);
		}
		structType->setBody(types, false);
		for (auto& member : node.branch[MEMBERS].branch) {
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
class StructNode :public Codegen {
private:
public:
	enum BRANCH {
		NAME,
		MEMBERS
	};
	llvm::Value* codegen(CodeGenerator& cg, Node node)override {
		auto* structType = llvm::StructType::create(cg.getBuilder().getContext(), node.branch[NAME].value);
		cg.getType().emplace(structType->getName().str(), structType);
		std::vector <llvm::Type* > types;
		cg.getStructMember().emplace(structType->getName().str(), std::unordered_map<std::string, unsigned>{});
		for (unsigned hash = 0; auto & member : node.branch[MEMBERS].branch) {
			if (member.node != NODE::FUNCTION) {
				types.push_back(cg.getType()(member.branch[TypeIdentNode::TYPE].linkBranchStr()));
				cg.getStructMember()[structType->getName().str()].emplace(member.branch[TypeIdentNode::NAME].value, hash);
				++hash;
			}
		}
		structType->setBody(types, false);
		for (auto& member : node.branch[MEMBERS].branch) {
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
				, node.branch.size() == 4
			)
		);
	}
};
class JIT {
private:
	llvm::ExecutionEngine* engine;
	llvm::Function* func;
public:
	JIT(std::unique_ptr<llvm::Module>& mainModule) {
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
	auto tokens = Lexer().tokenize(File("test.txt").read());
	auto iter = tokens.begin();
	auto number = BNF(TOKEN::NUMBER).regist(NODE::NUMBER);
	auto string = BNF(TOKEN::STRING).regist(NODE::STRING);
	auto type = BNF(TOKEN::IDENT).push()[(BNF("[").push() + number.push() + BNF("]").push()).loop()][BNF("*").push().loop()];
	auto variable = BNF(TOKEN::IDENT).regist(NODE::VARIABLE);
	auto reference = (BNF("&") + variable).regist(NODE::REFERENCE);
	auto floatNum = (number.push() + BNF(".").push() + number.push()).regist(NODE::FLOATING_POINT);//.number|f
	auto intNum = (number.push() + BNF(TOKEN::IDENT).push()).regist(NODE::INT);
	BNF expr;
	auto call = (BNF(TOKEN::IDENT).push() + BNF("(")[(*expr).push()[BNF(",")].loop()].push() + BNF(")")).regist(NODE::CALL);
	auto arrayAccess = (variable.regist(NODE::REFERENCE).push() + (BNF("[") + (*expr).push() + BNF("]")).loop().push()).regist(NODE::ARRAY_ACCESS);
	auto member = ((call | variable.regist(NODE::REFERENCE)).push() + ((BNF(".") + (call | variable.regist(NODE::REFERENCE))).push().loop())).regist(NODE::MEMBER);
	auto arrayExpr = (BNF("[") + ((*expr).push()[BNF(",")]).loop() + BNF("]")).regist(NODE::ARRAY);
	auto structInit = (BNF(TOKEN::IDENT).push() + BNF("{") [((variable.push() +BNF(":") + (*expr).push()).push()[BNF(",")]).loop()].push() + BNF("}")).regist(NODE::STRUCT_INIT);
	BNF  add;
	auto compare = ((*add).push() + BNF("<") + (*add).push()).regist(NODE::LESS) | (*add);
	auto let = (BNF("let") + BNF(TOKEN::IDENT).push() + BNF("=") + ((*expr).push().regist(NODE::SCALAR)).push()).regist(NODE::LET);
	auto assign = ((arrayAccess | member | variable.regist(NODE::REFERENCE)).push() + BNF("=") + (*expr).push()).regist(NODE::ASSIGN);
	auto primary = BNF("(") + (*compare).expect(BNF(")")) | intNum | floatNum | structInit | arrayExpr | arrayAccess.push().regist(NODE::ARRAY_ACCESS_LOAD) | member.push().regist(NODE::MEMBER_LOAD) | call | reference | variable | string;
	auto mul = (primary.push() + (BNF("*") + (*primary).push()).regist(NODE::MUL) | BNF("/") + (*primary).push().regist(NODE::DIV)) | primary;
	add = (mul.push() + (BNF("+") + (*add).push()).regist(NODE::ADD) | BNF("-") + (*add).push().regist(NODE::SUB)) | mul;
	auto ret = (BNF("return")[(*expr).push()]).regist(NODE::RETURN);
	auto block = (BNF("{")[(((*expr).push() + BNF(";")) | BNF(";")).loop()] + BNF("}")).regist(NODE::BLOCK);
	auto ifExpr = ((BNF("if")[BNF("(")] + (*expr).push()[BNF(")")] + (*expr).push()).push()[((BNF("elif") | BNF("else") + BNF("if"))[BNF("(")] + (*expr).push()[BNF(")")] + block.push()).push().loop()][BNF("else") + block.push()]).regist(NODE::IF);
	auto whileExpr = (BNF("while")[BNF("(")] + (*expr).push()[BNF(")")] + block.push()).regist(NODE::WHILE);
	expr = ret | let | whileExpr | ifExpr | assign | compare | block;
	auto externFunc = (BNF("extern") + type + BNF(TOKEN::IDENT).push() + BNF("(")[(type).push()[BNF(",")].loop()].push()[(BNF(".") + BNF(".") + BNF(".")).push()] + BNF(")") + BNF(";")).regist(NODE::EXTERN);
	auto function = (BNF("fn") + BNF(TOKEN::IDENT).push() + BNF("(")[(type.push() + BNF(TOKEN::IDENT).push())[BNF(",")].push().loop()].push() + BNF(")")[BNF("-") + BNF(">") + type].push() + block.push()).regist(NODE::FUNCTION);
	auto memberRegist = (type.push() + BNF(TOKEN::IDENT).push() + BNF(";")).regist(NODE::MEMBER_REGIST);
	auto structExpr = (BNF("struct") + BNF(TOKEN::IDENT).push() + BNF("{")[(memberRegist | function).push().loop()].push() + BNF("}")).regist(NODE::STRUCT);
	auto accessExpr = ((BNF("private") | BNF("public") | BNF("protected")).push() + BNF(":")).regist(NODE::CLASS_ACCESS);
	auto classExpr = (BNF("class") + BNF(TOKEN::IDENT).push() + BNF("{")[accessExpr.push() + (accessExpr | memberRegist | function).push().loop()].push() + BNF("}")).regist(NODE::CLASS);
	//auto constructor = (type.push() + call.push()).regist(NODE::CONSTRUCTOR);
	auto program = (classExpr|structExpr | externFunc | function).push().regist(NODE::BLOCK).loop();
	CodeGenerator codegen;
	codegen.setDestructorCallback([&codegen,&call](std::string name,llvm::Value* value) {
		if (!(value &&
			name!="0"&&
			name!="this"&&
			name!="return"&&
			value->getType()->isPointerTy() &&
			value->getType()->getNonOpaquePointerElementType()->isStructTy() &&
			codegen.getClasses().is_class(std::move(value->getType()->getNonOpaquePointerElementType()->getStructName().str())))) {
			return;
		}
		codegen.registTask(
			[&codegen, value]() {
				codegen.getBuilder().CreateCall(
					codegen.getModule()->getFunction(
						std::move(value->getType()->getNonOpaquePointerElementType()->getStructName().str()) + "_destructor"
					),
					{ value });
			}
		);
		});
	codegen.emplace<NoneNode>(NODE::NONE);
	codegen.emplace<ExternNode>(NODE::EXTERN);
	codegen.emplace<FunctionNode>(NODE::FUNCTION);
	codegen.emplace<CallNode>(NODE::CALL);
	codegen.emplace<RetNode>(NODE::RETURN);
	codegen.emplace<BlockNode>(NODE::BLOCK);
	codegen.emplace<StringNode>(NODE::STRING);
	codegen.emplace<DoubleNode>(NODE::FLOATING_POINT);
	codegen.emplace<IntNode>(NODE::INT);
	codegen.emplace<ClassNode>(NODE::CLASS);
	codegen.emplace<ConstructorNode>(NODE::CONSTRUCTOR);
	codegen.emplace<StructNode>(NODE::STRUCT);
	codegen.emplace<StructInitNode>(NODE::STRUCT_INIT);
	codegen.emplace<MemberNode>(NODE::MEMBER);
	codegen.emplace<ArrayNode>(NODE::ARRAY);
	codegen.emplace<ArrayAccessNode>(NODE::ARRAY_ACCESS);
	codegen.emplace<ScalarNode>(NODE::SCALAR);
	codegen.emplace<VariableNode>(NODE::VARIABLE);
	codegen.emplace<ReferenceNode>(NODE::REFERENCE);
	codegen.emplace<LetNode>(NODE::LET);
	codegen.emplace<DefineNode>(NODE::DEFINE);
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
	auto result = engine.run();
	llvm::outs() << "result int:" << result.IntVal << "\n"
		<< "result double:" << result.DoubleVal << "\n";
	llvm::outs().flush();
	return EXIT_SUCCESS;
}
/*
constructor a(){}
constructor(){}
fn constructor(){}
fn ClassName(){)}j
*/
/*
アクセスをカウントする(関数の返り値推論のときに+して関数を作り替えるときに-していく。
0になるとデストラクタが呼ばれる
指定されたカウントが過ぎるとそこでデストラクタがよｂっるjkkj
*/