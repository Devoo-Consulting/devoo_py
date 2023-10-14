#                  Monotone ONE-IN-THREE SAT Solver
#                          Frank Vega
#                        October 14, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import argparse
import sys
import z3
import time
z3.set_option(model=True)
#z3.set_option(precision=10)
#z3.set_option(rational_to_decimal=True)
z3.set_param("parallel.enable", False)
log = False
timed = False
started = 0.0

def logging(message, elapsed = 0.0):
    if log and timed and elapsed > 0.0:
        print(message + (f" timed {elapsed} milliseconds elapsed time" if timed else ""))
    elif log:
        print(message)

def solve(clauses, total):
    if timed:
        started = time.time()
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
    if timed:
        logging("Done building the linear system", time.time() - started)
    else:
        logging("Done building the linear system")

    if timed:
        started = time.time()

    logging("Start solving the linear system")    
    result = s.check()

    if timed:
        logging("Done solving the linear system", time.time() - started)
    else:
        logging("Done solving the linear system")
        
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

    parser = argparse.ArgumentParser(description='Solve an NP-complete problem from a DIMACS file.')
    parser.add_argument('-i', '--inputFile', type=str, help='Input file path', required=True)
    parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('-t', '--timer', action='store_true', help='Enable timer output')
    args = parser.parse_args()

    log = args.verbose
    timed = args.timer



    
    #Read and parse a dimacs file
    logging("Pre-processing started")
    if timed:
        started = time.time()

    reader = z3.Solver()
    reader.from_file(args.inputFile)
    #Format from dimacs
    asserts = reader.dimacs().splitlines()
    reader.reset()
    total = int(asserts[0].split(' ')[2])
    clauses = parse_dimacs(asserts[1:])

    if timed:
        duration = time.time() - started
        logging(f"Pre-processing done in: {duration} milliseconds elapsed time")
    else:
        logging("Pre-processing done")
    # NP-complete Solver
    solve(clauses, total)