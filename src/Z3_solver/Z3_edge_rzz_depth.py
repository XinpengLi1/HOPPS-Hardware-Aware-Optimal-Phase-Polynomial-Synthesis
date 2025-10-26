from z3 import Solver, Bool, Or, And, Sum, Not, Xor, set_param, Implies, AtLeast, AtMost, sat, Optimize, simplify
from functools import reduce
from qiskit import QuantumCircuit
from qiskit.circuit import Parameter
import numpy as np
import time
class z3_edge_rzz_depth:
    def __init__(self, num_qubit, layout=False, terms=False, G=False, I=False, rep = False):
        """
        Initializes the CNOT gate with bit-width for qubits.
        Args:
            num_qubit (int): the number of qubits of QAOA
            F (List): a list of term need to perform
            layout (List): a list of layout edges
            permutation (Boolean): if we need permutation
            G (list): a square matrix to control finial parity matrix
            I (list): a square matrix to control initial parity matrix
        """
        if G==False and  I==False:
            raise("Incomplete, Information, should initial input parity or output parity")
        self.bit_width = num_qubit
        self.finial_matrix = G
        self.initial_matrix = I
        self.terms = terms
        self.mixed_layer_identity = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        self.layout = layout
        self.layout_undirected = list({tuple(sorted(p)) for p in layout})
        self.rep = rep


        # self.mix_layer_matrix = [[True if i == j else False for j in range(num_qubit)] for i in range(num_qubit)]
        
        set_param("parallel.enable", True)
        # set_param("parallel.threads.max", 4)
        self.solver = Solver()

    def initialize_variables(self, K):
        """
        Initialize control qubit(q), target qubit(t), parity matrix(A), and intermediate expressions(h)
        """
        self.cnot = []
        self.rzz = []
        self.matrix_A = []
        for k in range(K):
            self.cnot.append([Bool(f"cnot_{k}_{i}") for i in range(len(self.layout))])
        for k in range(K):
            self.rzz.append([Bool(f"rzz_{k}_{i}") for i in range(len(self.layout_undirected))])
        for k in range(K+1):
            self.matrix_A.append([[Bool(f'matrix_A_{k+1}_{row_idx}_{col_idx}') for col_idx in range(self.bit_width)]
                for row_idx in range(self.bit_width)])
            
    def two_qubit_term(self, K):
        self.matrix_rzz = []
        for k in range(K):
            rzz_time = []
            for e in range(len(self.layout_undirected)):
                rzz_time.append([Bool(f"matrix_rzz_{k}_{e}_{j}") for j in range(self.bit_width)])
            self.matrix_rzz.append(rzz_time)

        for k in range(K):
            for e , (i,j) in  enumerate(self.layout_undirected):
                for f in range(self.bit_width):
                    self.solver.add(self.matrix_rzz[k][e][f] == And(self.rzz[k][e], Xor(self.matrix_A[k][i][f], self.matrix_A[k][j][f])))
            
    def term_check_clauses(self, K):
        self.term_zz_number = []
        for t in self.terms:
                self.solver.add(Or(
                [ 
                    And([
                        self.matrix_A[k][i][j] == t[j]
                        for j in range(self.bit_width)
                        ])               
                    for k in range(0, K+1) for i in range(self.bit_width)
                ] + 
                [   And([
                        self.matrix_rzz[k][e][j] == t[j]
                        for j in range(self.bit_width)
                        ])  
                     for k in range(0, K) for e , (_,_) in  enumerate(self.layout_undirected)
                ]
                ))
    
    # def rzz_cnot_conflict(self, K):
    #     for t in self.terms:
    #         for k in range(0, K):
    #             for e , (p, q) in  enumerate(self.layout_undirected):
    #                 # rzz_edge = [p,q]
    #                 # connected_cnot = []
    #                 # for i, (m,n) in enumerate(self.layout):
    #                 #     if m in rzz_edge or n in rzz_edge:
    #                 #         connected_cnot.append(self.cnot[k][i])

    #                 self.solver.add(Implies(And([
    #                     self.matrix_rzz[k][e][j] == t[j]
    #                     for j in range(self.bit_width)
    #                 ]), self.rzz[k][e]))
                    
    
    def constant_initial_clauses(self):
        if self.initial_matrix:
            for i in range(self.bit_width):
                for j in range(self.bit_width):
                    if self.initial_matrix[i][j] == True:  # Constant is True
                        self.solver.add(self.matrix_A[0][i][j])  # Single positive literal
                    elif self.initial_matrix[i][j] ==  False:
                        self.solver.add(Not(self.matrix_A[0][i][j]))  # Single negated literal
    
    def constant_finial_clauses(self, K):
        """
        Defines the final state clauses for all result qubits based on the CNOT operation.
        :param k: Number of CNOT gates.
        """
        if self.finial_matrix:
            for i in range(self.bit_width):
                for j in range(self.bit_width):
                    if self.finial_matrix[i][j] == True:  # Constant is True
                        self.solver.add(self.matrix_A[K][i][j])  # Single positive literal
                    elif self.finial_matrix[i][j] ==  False:
                        self.solver.add(Not(self.matrix_A[K][i][j]))  # Single negated literal 
    
    def depend_finial_clauses(self, K, rep):
        """
        Defines the final state clauses for all result qubits based on the CNOT operation.
        :param k: Number of CNOT gates.
        """
        for block in rep:
            rows = block['rows']
            for i in rows:
                subcolumns = block['columns_relate']
                for p , r in zip(block['columns'],  block['relate']):
                    xor_entry = []
                    for j, rr in zip(subcolumns, r):
                        if rr == 1:
                            xor_entry.append(self.matrix_A[K][i][j])
                    if xor_entry:
                        self.solver.add(self.matrix_A[K][i][p] == reduce(Xor,xor_entry))

    def validity_clauses(self, K):
        """
        Making sure each cnot is valid
        """
        for k in range(K): 
            # self.solver.add(AtMost(*self.cnot[k],1))
            for q in range(self.bit_width):
                connected_gates = []
                # connected_rzz = []
                for i, (m,n) in enumerate(self.layout):
                    if m == q or n == q:
                        connected_gates.append(self.cnot[k][i])
                for i, (m,n) in enumerate(self.layout_undirected):
                    if m == q or n == q:
                        connected_gates.append(self.rzz[k][i])
                self.solver.add(AtMost(*connected_gates,1))

            all_gates = self.cnot[k]+self.rzz[k]
            self.solver.add(AtLeast(*all_gates,1))

    def dependency_clauses(self, K):
        """
        Encodes dependencies between the results of consecutive CNOT gates.
        :param k: Number of CNOT gates.
        """
        for k in range(K):
            for e , (i,j) in  enumerate(self.layout):
                for r in range(self.bit_width):
                    self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][j][r] != self.matrix_A[k+1][j][r] ))
                    self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][j][r] == self.matrix_A[k+1][j][r] ))
            for q in range(self.bit_width):
                connected_cnot = []
                for i, (m,n) in enumerate(self.layout):
                    if n == q:
                        connected_cnot.append(self.cnot[k][i])  
                for r in range(self.bit_width):
                    self.solver.add(Implies(Not(Or(connected_cnot)), self.matrix_A[k][q][r] == self.matrix_A[k+1][q][r]))

        # for k in range(K): 
        #     for e , (i,j) in  enumerate(self.layout):
        #         for p in range(self.bit_width):
        #             if p == j:
        #                 for r in range(self.bit_width):
        #                     self.solver.add(Implies(And(self.cnot[k][e], self.matrix_A[k][i][r]), self.matrix_A[k][p][r] != self.matrix_A[k+1][p][r] ))
        #                     self.solver.add(Implies(And(self.cnot[k][e], Not(self.matrix_A[k][i][r])), self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r] ))
        #             else:
        #                 for r in range(self.bit_width):
        #                     self.solver.add(Implies(self.cnot[k][e], self.matrix_A[k][p][r] == self.matrix_A[k+1][p][r]))
    def num_cnot_assumption(self, n, K):
        cnots = []
        for k in range(K):
            for e , (i,j) in  enumerate(self.layout):
                cnots.append(self.cnot[k][e])
            for e , (i,j) in  enumerate(self.layout_undirected):
                cnots.append(self.rzz[k][e])
        return AtMost(*cnots, n)

    
    def solve(self, k, display=True):
        self.initialize_variables(k)
        self.constant_finial_clauses(k)
        self.constant_initial_clauses()
        self.two_qubit_term(k)
        if self.terms:
           self.term_check_clauses(k)
        #    self.rzz_cnot_conflict(k)
        self.validity_clauses(k)
        self.dependency_clauses(k)
        if self.rep is not False:
            self.depend_finial_clauses(k, self.rep)
        
        start_time = time.time()
        sat_or = str(self.solver.check()) 
        end_time = time.time() 
        
        elapsed_time = end_time - start_time

        if display:
                print(f"Elapsed time: {elapsed_time:.6f} seconds")

        if sat_or == "sat":
            if display:
                print("solution found for " + str(k)+ "current cnot: "+str(self.count_cnot(k)))
            count_cnot = self.count_cnot(k)
            if count_cnot<=1:
                self.model = self.solver.model()
                return True, k, elapsed_time, self.model
            for i in range(count_cnot, -1, -1):
                self.solver.add(self.num_cnot_assumption(i, k))
                sat_or_cnot = str(self.solver.check()) 
                if sat_or_cnot != "sat":
                    if display:
                        print("Try " +str(i)+ " cnots, fail")
                    return True, k, elapsed_time, self.model
                else:
                    self.model = self.solver.model()
                    if display:
                        print("Try " +str(i)+ " cnots, success")
        else:
            if display:
                print("No solution found for " + str(k))
            return False, k, elapsed_time, None
    
    def extract_parity_matrix_at_time(self, m):
        model = self.model
        A0 = np.zeros([self.bit_width,self.bit_width])
        for i in range(self.bit_width):
            for j in range(self.bit_width):
                if str(model[self.matrix_A[m][i][j]]) == 'True':
                    A0[i][j] = 1
        return [list(map(bool, a)) for a in A0]
    
    def count_cnot(self, K):
        model = self.solver.model()
        # model = self.model
        total_cnot = 0
        for k in range(K):
            for i in range(len(self.layout)):
                total_cnot += bool(model[self.cnot[k][i]])
            for i in range(len(self.layout_undirected)):
                total_cnot += bool(model[self.rzz[k][i]])
        return total_cnot
    
    def extract_quantum_circuit_from_model(self, K, theta):
        qc = QuantumCircuit(self.bit_width)
        model = self.model
        term_check = [False  for _ in range(len(self.terms))]

        for k in range(K+1):
            # Add Cnot gate
            if k>0:

                for e in range(len(self.layout_undirected)):
                #     if model[self.rzz[k-1][e]] == True:
                #         qc.rzz(theta[n],self.layout_undirected[e][0],self.layout_undirected[e][1])

                    matrix_rzz_row = []
                    for j in range(self.bit_width):
                        matrix_rzz_row.append(model[self.matrix_rzz[k-1][e][j]])
                    for n in range(len(self.terms)):
                        if term_check[n]==False and self.terms[n] == matrix_rzz_row:
                            qc.rzz(theta[n],self.layout_undirected[e][0],self.layout_undirected[e][1])
                            term_check[n]=True
                            break

                for n, (i,j) in enumerate(self.layout):
                    if model[self.cnot[k-1][n]] == True:
                        qc.cx(i,j)

            # Add parameters
            for i in range(self.bit_width):
                matrix_A_k_row = []
                for j in range(self.bit_width):
                    matrix_A_k_row.append(model[self.matrix_A[k][i][j]])
                for n in range(len(self.terms)):
                    if term_check[n]==False and self.terms[n] == matrix_A_k_row:
                        qc.rz(theta[n],i)
                        term_check[n]=True
                        break                                   
        return qc