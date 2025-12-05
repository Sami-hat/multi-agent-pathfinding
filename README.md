# Multi-Agent Pathfinding
Declarative Multi-Agent Multi-Objective Pathfinding Constraint Optimisation

## Overview

This project solves constraint satisfaction problems using Savile Row and Essence Prime. The repository contains model definitions and supporting tools for automated constraint solving.

## Structure

```
/src/model.eprime    - Essence Prime model definition
/savillerow/         - Savile Row constraint solver
/essence-prime/      - Essence Prime tools and libraries
/instances/          - Selected test layouts
```

## Requirements

- Savile Row constraint solver
- Essence Prime toolchain
- Java Runtime Environment (for Savile Row)

## Usage

Run the solver on your model:

```bash
savillerow model.eprime
```

The solver translates Essence Prime models into constraint problems and finds solutions.

## Model Development

Write your constraints in `src/model.eprime` using Essence Prime syntax. Define:

- Decision variables
- Domains
- Constraints
- Objective functions (optional)

## Output

Solutions appear in the output directory after solving completes. 

Build more complex instances and experiment with different solvers.

Check solution files for variable assignments that satisfy all constraints.
