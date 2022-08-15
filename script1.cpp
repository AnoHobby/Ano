#include <iostream>
#include <string>
#include <utility>
#include <regex>
#include <stack>
#include <unordered_map>
#include <any>
#include <windows.h>
template <typename T>
auto resizeAssign(std::vector<T> &vec,size_t index,T value) {
	if (vec.size() <= index) {
		vec.resize(index+1);
	}
	return vec[index] = value;
}
template <class T>
concept AddC = requires(T t) {
	t + t;
};
template <class T>
concept SubC = requires(T t) {
	t - t;
};
template <class T>
concept MulC = requires(T t) {
	t* t;
};
template <class T>
concept DivC = requires(T t) {
	t / t;
};
class Any {
private:
	class Base {
	public:
		virtual ~Base() {}
		virtual std::unique_ptr<Base> clone() = 0;
		virtual Any add(Any&) = 0;
		virtual Any sub(Any&) = 0;
		virtual Any mul(Any&) = 0;
		virtual Any div(Any&) = 0;
	};
	template <class T>
	class Derived :public Base {
	private:
		T value;
		template <bool T>
		class Implement {
		private:
		public:
			//template <class TFR,class... TFA, class FFR, class... FFA >
			//auto operator()(std::function<TFR(TFA...)> trueFunc, std::function<FFR(FFA...)>  falseFunc,TFA... trueFuncArg,FFA... falseFuncArg) {//引数を変えたい場合これだとfunctionを自動で作ってくれないからエラー
			//	return falseFunc(falseFuncArg...);
			//}
		};
		template <>
		class Implement<false> {
		private:
		public:
			template <class TF, class FF, class... A>
			auto operator()(TF trueFunc, FF falseFunc, A... arguments) {
				return falseFunc(arguments...);
			}
		};
		template <>
		class Implement<true> {
		private:
		public:
			template <class TF, class FF, class... A>
			auto operator()(TF trueFunc, FF falseFunc, A... arguments) {
				return trueFunc(arguments...);
			}
		};
	public:
		Derived(T const& value) :value(value) {}
		T get() {
			return value;
		}
		std::unique_ptr<Base> clone()override {
			return std::make_unique<Derived<T> >(value);
		}
		Any add(Any& any) override {
			return Implement<AddC<T> >()([](auto value, auto any) {return Any(value + any.get<T>()); }, [](auto value, auto any) {return any; }, value, any);
		}
		Any sub(Any& any) override {
			return Implement<SubC<T> >()([](auto value, auto any) {return Any(value - any.get<T>()); }, [](auto value, auto any) {return any; }, value, any);;
		}
		Any mul(Any& any) override {
			return Implement<MulC<T> >()([](auto value, auto any) {return Any(value * any.get<T>()); }, [](auto value, auto any) {return any; }, value, any);;
		}
		Any div(Any& any) override {
			return Implement<DivC<T> >()([](auto value, auto any) {return Any(value / any.get<T>()); }, [](auto value, auto any) {return any; }, value, any);;
		}
	};
	std::unique_ptr<Base> data;
public:
	template <class T>
	Any(T const& value) :data(std::make_unique<Derived<T> >(value)) {

	}
	Any() {}
	Any(const Any& any) {
		data = any.data->clone();
	}
	template <class T>
	auto operator=(T value) {
		data = std::make_unique<Derived<T> >(value);
	}
	auto operator=(const Any& any) {
		data = any.data->clone();
	}
	auto operator+(Any& any) {
		return data->add(any);
	}
	auto operator-(Any& any) {
		return data->sub(any);
	}
	auto operator*(Any& any) {
		return data->mul(any);
	}
	auto operator/(Any& any) {
		return data->div(any);
	}
	template <class T>
	auto get() {
		auto p = dynamic_cast<Derived<T> *>(data.get());
		return p->get();
	}
};
enum class TOKEN {
	T_EOF,
	NUMBER,
	RESERVED,
	VARIABLE
};
class Token {
private:
public:
	auto tokenize(std::string source) {
		std::vector<std::pair<TOKEN,std::string> > data;
		auto check = [&](auto t,auto r) {
			std::smatch m;
			if (!std::regex_search(source, m, r))return false;
			data.push_back({ t,m[0].str() });
			source = source.substr(m[0].str().size());
			return true;
		};
		for (; source.size();) {
			if (check(TOKEN::NUMBER, std::regex(R"(^\d+)"))) {
				continue;
			}
			else if (check(TOKEN::RESERVED,std::regex(R"(^(func|return|else|while|if|==|<=|>=|!=|[{}+-/*\(\)=<>]))"))) {
				continue;
			}
			else if (check(TOKEN::VARIABLE,std::regex(R"(^[a-zA-Z_][\w]*)"))) {//\s^/d
				continue;
			}
			source = source.substr(1);
		}
		data.push_back({ TOKEN::T_EOF,"" });
		return data;
	}
};
enum class NODE {
	NUMBER,//std::pair<numbr,int>
	ADD,
	SUB,
	MUL,
	DIV,
	VARIABLE,
	ASSIGN,
	EQUAL,
	NOT_EQUAL,
	LESS,
	EQUAL_LESS,
	IF,
	ELSE,
	WHILE,
	BLOCK,
};
class Node {
private:
public:
	NODE node;
	std::vector<Node > access;
	Any value;
};
class Perser {
private:
	std::vector<std::pair<TOKEN, std::string> > data;
	decltype(data.begin()) iter;
	auto number() {
		Node node;//*iter++でもいいかも
		node.node = NODE::NUMBER;
		node.value = std::stoi((*iter).second);
		++iter;
		return node;
	}
	Node primary();
	Node unary();
	Node ifExpr();
	Node whileExpr();
	Node block();
	auto mul() {
		auto node = unary();
		while (true) {
			if ((*iter).second == "*"&& data.end() >= iter + 1) {
				++iter;
				resizeAssign(node.access, 0, node);
				resizeAssign(node.access, 1, unary());
				node.node = NODE::MUL;
			}
			else if ((*iter).second == "/" && data.end() >= iter + 1) {
				++iter;
				resizeAssign(node.access, 0, node);
				resizeAssign(node.access, 1, unary());
				node.node = NODE::DIV;
			}
			else {
				break;
			}

		}
		return node;
	}
	auto add() {
		auto node = mul();
		while (true) {
			if ((*iter).second == "+"&& data.end() >= iter + 1) {
				++iter;
				resizeAssign(node.access, 0, node);
				resizeAssign(node.access, 1, mul());
				node.node = NODE::ADD;
			}
			else if ((*iter).second == "-"&& data.end() >= iter + 1) {
				++iter;
				resizeAssign(node.access, 0, node);
				resizeAssign(node.access, 1, mul());
				node.node = NODE::SUB;
			}
			else {
				break;
			}
		}
		return node;
	}
	auto compare() {
		auto node = add();
		auto editNode = [&](bool swap,NODE flag) {
			++iter;
			resizeAssign(node.access, 0^swap, node);
			resizeAssign(node.access, 1^swap, add());
			node.node = flag;
		};
		if ((*iter).second=="==") {
			editNode(false,NODE::EQUAL);
		}
		else if ((*iter).second == "!=") {
			editNode(false, NODE::NOT_EQUAL);
		}
		else if ((*iter).second == "<") {
			editNode(false, NODE::LESS);
		}
		else if ((*iter).second == "<=") {
			editNode(false, NODE::EQUAL_LESS);
		}
		else if ((*iter).second == ">") {
			editNode(true, NODE::LESS);
		}
		else if ((*iter).second == ">=") {
			editNode(true, NODE::EQUAL_LESS);
		}
		return node;
	}
	auto variable() {
		Node node;
		node.node = NODE::VARIABLE;
		node.value = (*iter).second;
		++iter;
		return node;
	}
	auto expr() {
		if (data.end() >= iter + 2 && (*iter).first == TOKEN::VARIABLE && (*(1 + iter)).second == "=") {
			auto node = variable();
			++iter;
			resizeAssign(node.access, 0, node);
			resizeAssign(node.access, 1, compare());
			//Node node;
			//node.node = NODE::VARIABLE;
			//node.value = (*(iter)).second;
			//iter += 2;
			//resizeAssign(node.access, 0, variable());
			//resizeAssign(node.access, 1, compare());
			node.node = NODE::ASSIGN;
			return node;
		}
		else if ((*iter).second == "if") {
			++iter;
			return ifExpr();
		}
		else if (iter->second == "while") {
			++iter;
			return whileExpr();
		}
		else if (iter->second=="{") {
			++iter;
			return block();
		}
		return compare();
	}
public:
	Perser(decltype(data) data):data(data),iter(this->data.begin()) {

	}
	auto perser() {
		std::vector<Node > nodes;
		nodes.push_back(expr());
		while ((*iter).second == ","&&data.end() >= iter + 1) {
			++iter;
			nodes.push_back(expr());
		}
		return nodes;
	}
};
Node Perser::unary() {
	if ((*iter).second == "+" && data.end() >= iter + 1) {//よくgithubみてみな
		++iter;
		return primary();
	}
	else if ((*iter).second == "-" && data.end() >= iter + 1) {
		++iter;
		Node node;
		node.node = NODE::NUMBER;
		node.value = 0;
		resizeAssign(node.access,0,node);
		node.node = NODE::SUB;
		resizeAssign(node.access, 1, primary());
		return node;
	}
	return primary();
}
Node Perser::primary() {
	if ((*iter).second == "("&& data.end() >= iter + 1) {
		++iter;
		auto node=compare();
		++iter;
		return node;
	}
	else if (TOKEN::VARIABLE == (*iter).first&& data.end() >= iter + 1) {//(*iter++)
		return variable();
	}
	return number();
}
Node Perser::ifExpr() {
	iter = ++std::find(iter, data.end(), std::pair{ TOKEN::RESERVED,std::string("(") });
	auto node = compare();
	iter = ++std::find(iter, data.end(), std::pair{ TOKEN::RESERVED,std::string(")") });
	auto expression = expr();
	if ((*(1+iter)).second == "else") {
		iter+=3;
		auto exprElse = expr();
		resizeAssign(exprElse.access,0,expression);
		resizeAssign(exprElse.access, 1, exprElse);
		exprElse.node = NODE::ELSE;
		resizeAssign(node.access, 0, node);
		resizeAssign(node.access, 1, exprElse);
		node.node = NODE::IF;
		return node;
	}
	resizeAssign(node.access, 0, node);
	resizeAssign(node.access, 1, expression);
	node.node = NODE::IF;
	return node;
	//if (find == data.end());
}
Node Perser::whileExpr() {
	++iter;//(
	auto node = compare();
	++iter;//)
	resizeAssign(node.access, 0, node);
	resizeAssign(node.access, 1, expr());
	node.node = NODE::WHILE;
	return node; 
}
Node Perser::block() {
	auto node = expr();
	while (iter->second == ",") {
		++iter;
		resizeAssign(node.access, 0, node);
		resizeAssign(node.access, 1, expr());
		node.node = NODE::BLOCK;
	}
	++iter;//}
	return node;

}
enum class OPERATION {
	PUSH,
	POP,
	ADD,
	SUB,
	MUL,
	DIV,
	LOAD,
	STORE,
	PUSH_I,
	EQUAL,
	NOT_EQUAL,
	LESS,
	EQUAL_LESS,
	JUMP,
	JZ,
	DUMMY
};
class Operation {
private:
public:
	OPERATION opCode;
	std::vector<DWORD> operands;
	Operation(decltype(opCode) opCode, decltype(operands) operands):opCode(opCode),operands(operands) {

	}
};
class Generator {
private:
	std::vector<Operation> operations;
	std::unordered_map<std::string,int> variables;
	unsigned int offset,label;
	auto getVar(decltype(variables)::key_type variable) {
		if (!variables.count(variable)) {
			variables.emplace(variable, offset++);
		}
		operations.push_back(Operation(OPERATION::PUSH_I, { (DWORD)variables.at(variable) }));//kyasuto
	}
public:
	std::vector<Operation> codegen(Node node) {
		//ここにoperations入れる場合は返り血を連結する
		switch (node.node) {
		case NODE::NUMBER:
			operations.push_back(Operation(OPERATION::PUSH_I, { (DWORD)node.value.get<int>()}));
			break;
		case NODE::ADD:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::POP, { 1 }));
			operations.push_back(Operation(OPERATION::ADD, { 0,1 }));
			break;
		case NODE::MUL:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::POP, { 1 }));
			operations.push_back(Operation(OPERATION::MUL, { 0,1 }));
			break;
		case NODE::SUB:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::POP, { 1 }));
			operations.push_back(Operation(OPERATION::SUB, { 1,0 }));
			break;
		case NODE::DIV:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::POP, { 1 }));
			operations.push_back(Operation(OPERATION::DIV, { 1,0 }));
			break;
		case NODE::ASSIGN:
			getVar(node.access[0].value.get<std::string>());
			codegen(node.access[1]);
			operations.push_back(Operation{ OPERATION::POP, {1} });
			operations.push_back(Operation{ OPERATION::POP, {0} });
			operations.push_back(Operation{ OPERATION::STORE, {0,1 } });
			operations.push_back(Operation{ OPERATION::PUSH, {1} });
			break;
		case NODE::VARIABLE:
			getVar(node.value.get<std::string>());
			operations.push_back(Operation{ OPERATION::POP, {0} });
			operations.push_back(Operation{ OPERATION::LOAD, {1,0} });
			operations.push_back(Operation{ OPERATION::PUSH, {1} });
			break;
		case NODE::EQUAL:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation{OPERATION::POP,{0}});
			operations.push_back(Operation{ OPERATION::POP,{1} });
			operations.push_back(Operation{ OPERATION::EQUAL,{1,0} });
			break;
		case NODE::NOT_EQUAL:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation{ OPERATION::POP,{0} });
			operations.push_back(Operation{ OPERATION::POP,{1} });
			operations.push_back(Operation{ OPERATION::NOT_EQUAL,{1,0} });
			break;
		case NODE::LESS:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation{ OPERATION::POP,{0} });
			operations.push_back(Operation{ OPERATION::POP,{1} });
			operations.push_back(Operation{ OPERATION::LESS,{1,0} });
			break;
		case NODE::EQUAL_LESS:
			codegen(node.access[0]);
			codegen(node.access[1]);
			operations.push_back(Operation{ OPERATION::POP,{0} });
			operations.push_back(Operation{ OPERATION::POP,{1} });
			operations.push_back(Operation{ OPERATION::EQUAL_LESS,{1,0} });
			break;
		case NODE::IF:
			codegen(node.access[0]);
			operations.push_back(Operation(OPERATION::POP,{0}));
			if (node.access[1].node == NODE::ELSE) {
				auto label1 = label++, label2 = label++;
				operations.push_back(Operation{ OPERATION::JZ,{0,label1}});
				codegen(node.access[1].access[0]);
				operations.push_back(Operation(OPERATION::POP,{0}));
				operations.push_back(Operation(OPERATION::JUMP, { label2 }));
				operations.push_back(Operation(OPERATION::DUMMY,{label1 }));
				codegen(node.access[1].access[1]);
				operations.push_back(Operation(OPERATION::POP, { 0 }));
				operations.push_back(Operation(OPERATION::DUMMY, { label2 }));
			}
			else {
				auto label1 = label++;
				operations.push_back(Operation(OPERATION::JZ, { 0,label1 }));
				codegen(node.access[1]);
				operations.push_back(Operation(OPERATION::POP, { 0 }));
				operations.push_back(Operation(OPERATION::DUMMY, { label1 }));

			}
			operations.push_back(Operation(OPERATION::PUSH_I, { 0 }));
			break;
		case NODE::WHILE:
		{
			auto label1 = label++, label2 = label++;
			operations.push_back(Operation(OPERATION::DUMMY, { label1 }));
			codegen(node.access[0]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::JZ, { 0, label2 }));
			codegen(node.access[1]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			operations.push_back(Operation(OPERATION::JUMP, { label1 }));
			operations.push_back(Operation(OPERATION::DUMMY, { label2 }));
			operations.push_back(Operation(OPERATION::PUSH_I, { 0 }));
		}
			break;
		case NODE::BLOCK:
			codegen(node.access[0]);
			operations.push_back(Operation(OPERATION::POP, { 0 }));
			codegen(node.access[1]);
			break;
		}

		return operations;
	}
	std::vector<Operation> codegen(std::vector<Node > nodes) {
		for (auto& node : nodes) {
			codegen(node);
			operations.push_back(Operation(OPERATION::POP,{0}));
		}
		return operations;
	}
};
class VM {
private:
	std::stack<decltype(Operation::operands)::value_type> stack;
	std::vector<DWORD> reg;
	std::vector<DWORD> val;
public:
	auto run(std::vector<Operation> code) {
		std::unordered_map<int, decltype(code)::iterator > labels;
		for (auto op = code.begin(); op != code.end();++op) {
			if ((* op).opCode == OPERATION::DUMMY) {
				labels.insert_or_assign((* op).operands[0], op);
			}
		}
		for (auto op = code.begin(); op != code.end(); ++op) {
			switch (op->opCode) {
			case OPERATION::PUSH:
				stack.push(reg[op->operands[0]]);
				break;
			case OPERATION::POP:
				resizeAssign(reg, op->operands[0], stack.top());
				stack.pop();
				break;
			case OPERATION::ADD:
				stack.push(reg[op->operands[0]]+ reg[op->operands[1]]);
				break;
			case OPERATION::MUL:
				stack.push(reg[op->operands[0]] * reg[op->operands[1]]);
				break;
			case OPERATION::SUB:
				stack.push(reg[op->operands[0]] - reg[op->operands[1]]);
				break;
			case OPERATION::DIV:
				stack.push(reg[op->operands[0]] / reg[op->operands[1]]);
				break;
			case OPERATION::PUSH_I:
				stack.push(op->operands[0]);
				break;
			case OPERATION::STORE:
				resizeAssign(val,reg[op->operands[0]], reg[op->operands[1]]);
				break;
			case OPERATION::LOAD:
				resizeAssign(reg, op->operands[0], val[reg[op->operands[1]]]);
				break;
			case OPERATION::EQUAL:
				stack.push(reg[op->operands[0]] == reg[op->operands[1]]);
				break;
			case OPERATION::NOT_EQUAL:
				stack.push(reg[op->operands[0]] != reg[op->operands[1]]);
				break;
			case OPERATION::LESS:
				stack.push(reg[op->operands[0]] < reg[op->operands[1]]);
				break;
			case OPERATION::EQUAL_LESS:
				stack.push(reg[op->operands[0]] <= reg[op->operands[1]]);
				break;
			case OPERATION::JUMP:
				op = labels[op->operands[0]];
				break;
			case OPERATION::JZ:
				if (0 != reg[op->operands[0]])break;
				op = labels[op->operands[1]];
				break;
			}
		}
		return reg[0];
		//auto output = stack.top();
		//stack.pop();
		//return output;
	}
};
int main() {
	Token token;
	Perser perser(token.tokenize(*std::istream_iterator<std::string>(std::cin)));
	//Perser perser(token.tokenize("if(0==0)val=10,val+1"));
	Generator generator;
	VM vm;
	//perser.perser();
	std::cout<<vm.run(generator.codegen(perser.perser()));
	//for (auto& [token, str] : token.tokenize(*std::istream_iterator<std::string>(std::cin))) {//token.tokenize(*std::istream_iterator<std::string>(std::cin))
	//	std::cout <<(int)token << "," << str << std::endl;
	//}
	return EXIT_SUCCESS;
}