NVFLAGS := -std=c++11 -lineinfo -O3 
TARGET := hw4

.PHONY: all
all: $(TARGET)

$(TARGET): hw4.cu
	nvcc $(NVFLAGS) -o $(TARGET) hw4.cu

# sha256.o: sha256.cu
# 	nvcc $(NVFLAGS) -c sha256.cu

clean:
	rm -rf hw4 *.o




