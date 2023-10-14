#                  Monotone ONE-IN-THREE SAT Solver
#                          Frank Vega
#                        October 14, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import sys
import z3
z3.set_option(model=True)
#z3.set_option(precision=10)
#z3.set_option(rational_to_decimal=True)
z3.set_param("parallel.enable", False)
log = False

def logging(message):
    if log:
        print(message)

def solve(clauses, total):
    logging("Start building the linear system")
    s = z3.Solver()
    x = [ z3.Real('x%s' % (i + 1)) for i in range(total) ]
    for i in range(total):
        s.add(x[i] >= 0.0)
    for list in clauses:
        s.add(x[list[0]-1] + x[list[1]-1] + x[list[2]-1] == 1.0)
        s.add(x[list[0]-1] + x[list[1]-1] > 2.0/3.0)
        s.add(x[list[0]-1] + x[list[2]-1] > 2.0/3.0)
        s.add(x[list[1]-1] + x[list[2]-1] > 2.0/3.0)
    logging("End building the linear system")    
    logging("Start solving the linear system")    
    result = s.check()
    logging("End solving the linear system")
    if result == z3.unsat:
        print("s UNSATISFIABLE")
    elif result == z3.unknown:
        print("s UNKNOWN")
    else:
        m = s.model()
        print("s SATISFIABLE")
        for d in m.decls():
            print ("%s = %s" % (d.name(), m[d]))   

def parse_dimacs(asserts):
    result = []
    for strvar in asserts:
        expr = strvar.split(" ")
        expr = expr[:-1]
        l = []
        for t in expr:
            v = int(t)
            l.append(v)
        result.append(l)        
    return result   
                       
if __name__ == "__main__":
    #Read and parse a dimacs file
    logging("Start reading and parsing dimacs file")
    temp = sys.argv[1]
    reader = z3.Solver()
    reader.from_file(temp)
    logging("End reading and parsing dimacs file") 
    #Format from dimacs
    logging("Start formating on dimacs")
    asserts = reader.dimacs().splitlines()
    reader.reset()
    total = int(asserts[0].split(' ')[2])
    clauses = parse_dimacs(asserts[1:])
    logging("End formating on dimacs")
    # NP-complete Solver
    solve(clauses, total)