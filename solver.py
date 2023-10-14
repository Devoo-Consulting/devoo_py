#                  Monotone ONE-IN-THREE SAT Solver
#                          Frank Vega
#                        October 14, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import sys
import z3
import time
z3.set_option(model=True)
#z3.set_option(precision=10)
#z3.set_option(rational_to_decimal=True)
z3.set_param("parallel.enable", False)
log = False
duration = 0.0

def logging(message, elapsed):
    if log:
        global duration
        print(message + " elapsed time " + str(elapsed - duration) + " milliseconds")
        duration = time.time()

def solve(clauses, total):
    logging("Start building the linear system", time.time())
    s = z3.Solver()
    x = [ z3.Real('x%s' % (i + 1)) for i in range(total) ]
    for i in range(total):
        s.add(x[i] >= 0.0)
    for list in clauses:
        s.add(x[list[0]-1] + x[list[1]-1] + x[list[2]-1] == 1.0)
        s.add(x[list[0]-1] + x[list[1]-1] > 2.0/3.0)
        s.add(x[list[0]-1] + x[list[2]-1] > 2.0/3.0)
        s.add(x[list[1]-1] + x[list[2]-1] > 2.0/3.0)
    logging("End building the linear system", time.time())    
    logging("Start solving the linear system", time.time())    
    result = s.check()
    logging("End solving the linear system", time.time())
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
    duration = time.time()
    #Read and parse a dimacs file
    logging("Start reading and parsing dimacs file", time.time())
    temp = sys.argv[1]
    reader = z3.Solver()
    reader.from_file(temp)
    logging("End reading and parsing dimacs file", time.time()) 
    #Format from dimacs
    logging("Start formating on dimacs", time.time())
    asserts = reader.dimacs().splitlines()
    reader.reset()
    total = int(asserts[0].split(' ')[2])
    clauses = parse_dimacs(asserts[1:])
    logging("End formating on dimacs", time.time())
    # NP-complete Solver
    solve(clauses, total)