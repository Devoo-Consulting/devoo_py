#                  Monotone ONE-IN-THREE 3SAT Solver
#                          Frank Vega
#                        October 14, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import argparse
import sys
import z3
import time

import reductor as N_SAT

z3.set_option(model=True)
#z3.set_option(precision=10)
#z3.set_option(rational_to_decimal=True)
z3.set_param("parallel.enable", False)
log = False
timed = False
started = 0.0

def logging(message):
    if log:
        print(message)


    
def solve_linear_system(s):

    logging("Start solving the linear system")  
    if timed:
        started = time.time()
    
    #Solve the linear system
    result = s.check()

    if timed:
        logging(f"Done solving the linear system in: {(time.time() - started) * 1000.0} milliseconds")
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

    # parser = argparse.ArgumentParser(description='Solve an NP-complete problem from a DIMACS file.')
    # parser.add_argument('-i', '--inputFile', type=str, help='Input file path', required=True)
    # parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    # parser.add_argument('-t', '--timer', action='store_true', help='Enable timer output')
    # args = parser.parse_args()

    log = True #args.verbose
    timed = True #args.timer
    file = "file.cnf"#args.inputFile

    #Read and parse a dimacs file
    logging("Pre-processing started")
    if timed:
        started = time.time()

    reader = z3.Solver()
    reader.from_file(file)
    #Format from dimacs
    asserts = reader.dimacs().splitlines()
    reader.reset()
    total = int(asserts[0].split(' ')[2])
    clauses = parse_dimacs(asserts[1:])

    if timed:
        logging(f"Pre-processing done in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Pre-processing done")

    # Polynomial Time Reduction from Monotone ONE-IN-THREE 3SAT to Linear programming
    logging("Start building the linear system")
    if timed:
        started = time.time()

    reduction = N_SAT.polynomial_time_reduction(clauses, total)
    reduction_S = N_SAT.polynomial_time_reduction_S(clauses, total)


    if timed:
        logging(f"Done building the linear system in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Done building the linear system")

    # Solve Linear programming in Polynomial Time
    solve_linear_system(reduction)
    solve_linear_system(reduction_S)