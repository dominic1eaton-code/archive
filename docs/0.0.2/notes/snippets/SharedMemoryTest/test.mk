CC=g++
CFLAGS  = -c -Wall -std=c++11 -lpthread -ltr
LDFLAGS = -lpthread -ltr 
SOURCES = testSM.cc SharedMemory.cc SharedMemoryExecution.cc
OBJECTS =$(SOURCES:.cpp=.o)
EXECUTABLE=MapReduce

all: $(SOURCES) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS) 
    $(CC) $(LDFLAGS) $(OBJECTS) -o $@

.cpp.o:
    $(CC) $(CFLAGS) $< -o $@
