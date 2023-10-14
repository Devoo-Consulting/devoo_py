import z3

def polynomial_time_reduction(clauses, total):

    # Build the linear system  
    s = z3.Solver()
    x = [ z3.Real('x%s' % (i + 1)) for i in range(total) ]
    for i in range(total):
        s.add(x[i] >= 0.0)
    for list in clauses:
        s.add(x[list[0]-1] + x[list[1]-1] + x[list[2]-1] == 1.0)
        s.add(x[list[0]-1] + x[list[1]-1] > 2.0/3.0)
        s.add(x[list[0]-1] + x[list[2]-1] > 2.0/3.0)
        s.add(x[list[1]-1] + x[list[2]-1] > 2.0/3.0)
    return s


def polynomial_time_reduction_S(clauses, total, sat = 3):
    # Build the linear system  
    s = z3.Solver()
    x = [z3.Real('x%s' % (i + 1)) for i in range(total)]
    for i in range(total):
        s.add(x[i] >= 0.0)
    for clause in clauses:
        clause_sum = z3.Sum([x[var-1] for var in clause])
        s.add(clause_sum == 1.0)
        for i in range(sat):
            for j in range(i+1, sat):
                s.add(x[clause[i]-1] + x[clause[j]-1] > (sat-1)/sat)
    return s