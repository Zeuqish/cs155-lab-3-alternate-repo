all:
	cargo llvm-cov --html && open ./target/llvm-cov/html/index.html