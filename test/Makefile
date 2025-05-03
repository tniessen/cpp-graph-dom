CXX ?= g++
CXXFLAGS ?= -std=c++20 -Wall -Wextra -pedantic

ifdef SANITIZER
  CXXFLAGS += -fsanitize=$(SANITIZER)
endif
ifdef DEBUG
  CXXFLAGS += -g -O0
else
  CXXFLAGS += -O3 -flto=auto
endif
ifdef GRAPH_DOM_NO_ASSERT
  CXXFLAGS += -DGRAPH_DOM_NO_ASSERT
endif

.PHONY: test
test: clean test-graph-dom
	@echo "================================================================="
	@./test-graph-dom
	@echo "================================================================="

test-graph-dom: test-graph-dom.cc ../graph-dom.h
	$(CXX) $(CXXFLAGS) -o $@ $<

.PHONY: clean
clean:
	rm -f test-graph-dom
