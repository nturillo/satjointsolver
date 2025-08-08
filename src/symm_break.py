# SymPy tool to generate CNF clauses for ordering extension vertex variables
import sys, json
from sympy.logic.boolalg import to_cnf, is_dnf, is_cnf
from sympy.logic import simplify_logic, Equivalent, And, Or, Not
from sympy import symbols

def order_pair(N, M, n, symbol_count):
    X = symbols([str(i) for i in range(symbol_count, symbol_count + n - 1)])
    clauses = [Or(M[0], ~N[0]), simplify_logic(Equivalent(X[0], Equivalent(N[0], M[0])), deep=True, force=True, form='cnf')]
    for i in range(n-2):
        clause = Equivalent(X[i+1], And(X[i], Equivalent(N[i+1], M[i+1])))
        clauses.append(simplify_logic(clause, deep=True, force=True, form='cnf'))
    for i in range(n-1):
        clause = Or(~X[i], M[i+1], ~N[i+1])
        clauses.append(clause)
    expr = And(*clauses)
    return to_cnf(expr, simplify=False, force=False)

def order_extension(X, symbol_count):
    # X is a 2D list of boolean variables where X[i][j] is the edge between
    # x_i and vertex j
    n = len(X[0])
    clauses = []
    for i in range(len(X) - 1):
        N = symbols([str(val) for val in X[i]])
        M = symbols([str(val) for val in X[i + 1]])
        clauses.append(order_pair(N, M, n, symbol_count))
        symbol_count += n - 1
    cnf_expr = to_cnf(And(*clauses), simplify=False, force=False)
    return cnf_to_dimacs(cnf_expr, symbol_count + n)

def cnf_to_dimacs(cnf_expr, var_count):
    """Convert a CNF SymPy expr to DIMACS string."""
    clauses = []
    if cnf_expr.func == And:
        clause_exprs = cnf_expr.args
    else:
        clause_exprs = (cnf_expr,)
    def lit_to_dimacs(lit):
        if lit.func == Not:
            return f"-{lit.args[0].name}"
        else:
            return f"{lit.name}"

    for clause in clause_exprs:
        if clause.func == Or:
            lits = [lit_to_dimacs(l) for l in clause.args]
        else:
            lits = [lit_to_dimacs(clause)]
        clauses.append(" ".join(lits) + " 0")

    dimacs_lines = []
    dimacs_lines.append(f"p cnf {var_count} {len(clauses)}")
    dimacs_lines.extend(clauses)
    return "\n".join(dimacs_lines)

if __name__ == "__main__":
    data = json.loads(sys.stdin.read())
    X = data["X"]
    symbol_count = data["symbol_count"]

    dimacs_str = order_extension(X, symbol_count)
    sys.stdout.write(dimacs_str)