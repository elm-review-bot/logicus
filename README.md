# LogicUS

## Design Goals

This package has been created to work with computer logic, specifically with propositional logic and first-order logic (in development). For a series of types and functions have been created that allow the definition and interpretation of formulas as well as the application of the main algorithms to reduce the consistency of formulas and sets.

## Overview

En los módulos creados se proporcionan las herramientas necesarias para la definición, ejecución y visualización de los principales algoritmos utilizados en el área al que van dedicados. En concreto:

### Propositional Logic

The _LogicUS.PL_ packages allow the definition of formulas and propositional sets on which a series of also implemented solving algorithms can be applied. Next, we make a synopsis of each of the modules exposed:

- **_LogicUS.PL.SintaxSemantics_**: Constituye la base de la lógica proposicional, de manera que en él se expone la sintáxis para la definición de las fórmulas así como la semántica para la interpretación de las mismas así como algun algoritmo básico en el ámbito de la lógica proposicional.

- **_LogicUS.PL.SemanticTableaux_**: It develops all the necessary tools for working with semantic boards, distinguishing the different types of formulas and rules and also allowing the visualization of the complete board.

- **_LogicUS.PL.NormalFormsClauses_**: It contains the functions necessary for the transformation of formulas into normal forms (negative, conjunctive and disjunctive). It also provides some functions that allow work with propositional clauses, definition, operations, transformation of formulas and sets into clausal sets, ...

- **_LogicUS.PL.DavisPutnamLogemannLovelan_**: It defines the functions necessary for the application of the DPLL solving algorithm to sets of propositional clauses as well as the search for models, based on this technique. Also, it allows the visualization of the complete board.

- **_LogicUS.PL.ResolutionStrategies_**: Define the functions for working with the resolution algorithms implementing different strategies: saturation, regular, best first, linear, positive, negative, unitary, by inputs, ...

### First Order Logic

In development. Available soon...
