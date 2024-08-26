# Inter-Procedural Constant Propagation

## Overview

Constant propagation is an optimization technique used in compilers to simplify expressions by substituting values of constants for their corresponding variables at compile time. This repository contains the implementation of an inter-procedural context-insensitive and flow-sensitive analysis pass along with a transformation pass for constant propagation in LLVM.

## Motivation

The primary objective of this optimization is to eliminate redundant computations by propagating constant values through the code, leading to optimized and efficient executable code. The provided example demonstrates the transformation of code by eliminating redundant computations and substituting constants.

## Directory Structure

```
├── InterProcConstProp
│   └── constprop.cpp
├── test
│   └── test_cases.ll
└── output
    └── transformed_test_cases.ll
```

- **test**: It contains the input IR (Intermediate Representation) code files for public test cases.
- **output**: It contains the transformed IR code files after running the optimization pass.
- **constprop.cpp**: The main implementation file for the constant propagation pass.

## Features

- **Inter-procedural Analysis:** Analyzes across function boundaries to propagate constants.
- **Context-Insensitive:** Treats all call sites of a function uniformly.
- **Flow-Sensitive:** Considers the flow of data within the program to propagate constants accurately.
- **Transformation Pass:** Substitutes computations with constant values based on the analysis.

## Example

### Original Code

```cpp
void main()
{
    int l = 40;
    fun(10, 100, 1000);
    bar(1000, 400, 300);
    foo(100, 400, 1000, l);
}

void fun(int i, int j, int k)
{
    bar(2000, i, 1000);
    int o = i * 2;
    int q = 2;
    int a = q * o * i;
    foo(100, a, k, 800);
}

void foo(int i, int j, int k, int x)
{
    x = i + j + k;
    printf("%d", x);
}

void bar(int i, int j, int k)
{
    j = (k * i) / 2;
    printf("%d", j);
}
```

### Optimized Code

```cpp
void main()
{
    fun(10, 100, 1000);
    bar(1000, 400, 300);
    foo(100, 400, 1000, 40);
}

void fun(int i, int j, int k)
{
    bar(2000, 10, 1000);
    foo(100, 400, 1000, 800);
}

void foo(int i, int j, int k, int x)
{
    printf("%d", 1500);
}

void bar(int i, int j, int k)
{
    j = (k * i) / 2;
    printf("%d", j);
}
```

## Pros

- The pre-existing LLVM constant propagation pass is not used.
- Utilised STL containers like `std::set`, `std::map`, and `std::vector`.
- Handled data types (boolean, integer, floats), operations (arithmetic, logical), and miscellaneous instructions (cast, load, store).
- Ensured variables are transformed to constants where applicable, including arguments passed to functions.

## Limitations

- Global Variables and Macros are not handled in this implementation.

## Getting Started

### Prerequisites

- LLVM development environment setup. For more details, visit this [link](https://www.llvm.org/docs/GettingStarted.html).
- C++ compiler that supports C++11 or later versions.
- Basic understanding of LLVM IR and compiler optimization techniques

### Building the Pass

1. Clone the repository.
2. Navigate to the directory and build the pass using CMake.
3. Run the pass using the `opt` tool on your target LLVM IR code.

### Usage

1. Compile your source code to LLVM IR.
2. Apply the constant propagation optimization pass.
3. Generate the optimized LLVM IR and compile it to the target executable.

## Contributing

Contributions are welcome! Please fork the repository, create a new branch, and submit a pull request with your changes.

## Acknowledgments

Special thanks to the LLVM community for their documentation and support.
