# devoo_py
Monotone ONE-IN-THREE SAT
----- 
Instance: A Boolean formula $\phi$ in 3CNF with no negated variables.

Question: Is there a truth assignment for $\phi$ such that each clause contains exactly one true literal?
 
**Remark: This problem is NP-complete (If any NP-complete can be solved in polynomial time, then $P = NP$)**.

- Note: This algorithm is based on the mathematical background of the following draft: [On Feasibly Solving NP-complete Problems](https://www.researchgate.net/publication/374551182_On_Feasibly_Solving_NP-complete_Problems) 

# Theory

- A literal in a Boolean formula is an occurrence of a variable or its negation. A Boolean formula is in conjunctive normal form, or CNF, if it is expressed as an AND of clauses, each of which is the OR of one or more literals. A truth assignment for a Boolean formula $\phi$ is a set of values for the variables in $\phi$. 

Example
----- 

Instance: The Boolean formula $(x_{1} \vee x_{2} \vee x_{3}) \wedge (x_{2} \vee x_{3} \vee x_{4}) \wedge (x_{3} \vee x_{4} \vee x_{5}) \wedge (x_{4} \vee x_{5} \vee x_{2}) \wedge (x_{5} \vee x_{1} \vee x_{2})$ where $\vee$ (OR) and $\wedge$ (AND) are logic operations.

Answer: The formula has a truth assignment such that each clause contains a true literal when only the variables $x_{1}$ and $x_{4}$ are true.

Input of this project
-----

The input is on [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) formula with the extension .cnf.
  
Let's take the **file.cnf** from our previous Boolean formula $(x_{1} \vee x_{2} \vee x_{3}) \wedge (x_{2} \vee x_{3} \vee x_{4}) \wedge (x_{3} \vee x_{4} \vee x_{5}) \wedge (x_{4} \vee x_{5} \vee x_{2}) \wedge (x_{5} \vee x_{1} \vee x_{2})$ is
```  
p cnf 5 5
1 2 3 0
2 3 4 0
3 4 5 0
4 5 2 0
5 1 2 0
```  

- The first line **p cnf 5 5** means there are 5 variables and 5 clauses.

- The second line **1 2 3 0** means the clause $(x_{1} \vee x_{2} \vee x_{3})$ (Note that, the number *0* means the end of the clause).

- ...

# Compile and Environment

Downloading and Installing
-----

Install at least Python 2.7 or a greater version until 3.10

Download and Install the following Number Theory Library 

- Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.

If you use pip, you can install Z3 with:
-----
```
pip install z3-solver
```

-----

# Build and Execute

To build and run from the command prompt:

```
git clone https://github.com/Devoo-Consulting/devoo_py.git
cd devoo_py
```

On Windows within devoo_py directory run

```
.\starexec_run_default.bat file.cnf
```

On Linux within devoo_py directory run

```
chmod +x starexec_run_default.sh
./starexec_run_default.sh file.cnf
```

Finally, it would obtain in the console output:

```
s SATISFIABLE
2 = 10000000000000001/30000000000000000
3 = 10000000000000001/30000000000000000
5 = 10000000000000001/30000000000000000
1 = 4999999999999999/15000000000000000
4 = 4999999999999999/15000000000000000
```

which means this is an instance of Monotone ONE-IN-THREE SAT just using the variables $x_{1}$ and $x_{4}$ as true (a variable is true when the real number output value is lesser than $\frac{1}{3}$)

# Code

- Python code by **Frank Vega**.

# Complexity

````diff
+ The reduction runs in polynomial time: We reduce Monotone ONE-IN-THREE SAT to a Linear System of Constraints.
- The whole polynomial time algorithm is based on the linear optimization with real variables without any objective to maximize or minimize.
````

# Acknowledgement

- The author wishes to thank the mathematician Arthur Rubin for his constructive comments and Luis Antonio Fonseca (CEO of DEVOO CONSULTING.) for his support.
 
# License
- MIT.
