.PHONY: all clean

all: prefault-heap prefault-stack-with-mlockall prefault-stack-without-mlockall
	sudo ./prefault-heap
	@echo
	@echo
	sudo ./prefault-stack-with-mlockall
	@echo
	@echo
	sudo ./prefault-stack-without-mlockall

clean:
	rm -f prefault-heap prefault-stack-with-mlockall prefault-stack-without-mlockall

prefault-heap: prefault-test.cc
	g++ -std=gnu++17 -o $@ $^

prefault-stack-with-mlockall: prefault-stack-test.cc
	g++ -std=gnu++17 -lpthread -DLOCK_MEMORY=1 -o $@ $^

prefault-stack-without-mlockall: prefault-stack-test.cc
	g++ -std=gnu++17 -lpthread -DLOCK_MEMORY=0 -o $@ $^
