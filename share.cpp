#pragma once
namespace share {
	template <class T>
	class Reverse {
	private:
		T& value;
	public:
		Reverse(T& value) :value(value) {}
		auto begin() {
			return value.rbegin();
		}
		auto end() {
			return value.rend();
		}
	};
}