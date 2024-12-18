    def PySAT_solver(self):
        """
        This is a WebAssembly power Python shell,
        where you can try the examples in the browser:
        1. Type code in the input cell and press
            Shift + Enter to execute;
        2. Or copy paste the code, and click on
            the "Run" button in the toolbar
        3. By the way, TAB-based autocompletion works!
        """

        # create a satisfiable CNF formula "(-x1 ∨ x2) ∧ (-x1 ∨ -x2)":
        cnf = CNF(from_clauses=[[1, 2]])

        # create a SAT solver for this formula:
        with Solver(bootstrap_with=cnf) as solver:
            # 1.1 call the solver for this formula:
            print('formula is', f'{"s" if solver.solve() else "uns"}atisfiable')
            print(solver.solve())
            # 1.2 the formula is satisfiable and so has a model:
            print('and the model is:', solver.get_model())

            # # 2.1 apply the MiniSat-like assumption interface:
            # print('formula is',
            #     f'{"s" if solver.solve(assumptions=[1, 2]) else "uns"}atisfiable',
            #     'assuming x1 and x2')

            # # 2.2 the formula is unsatisfiable,
            # # i.e. an unsatisfiable core can be extracted:
            # print('and the unsatisfiable core is:', solver.get_core())

    def generate_product(self, description):

        self.descr_temp = """
feature_model {
    Duck -> string ?
    Witch -> string ?
    Floats -> string ?
    [(Duck and Witch) or (!Duck and Floats)]
}
"""
        self.default_values = {
            'Fcard': {
                '*': {
                    'Type': 'IntRange',
                    'LowerBoundary': 0,
                    'UpperBoundary': 5
                },
                '+': {
                    'Type': 'IntRange',
                    'LowerBoundary': 1,
                    'UpperBoundary': 5
                },
                '?': {
                    'Type': 'Explicit',
                    'Values': [0, 1]
                }
            },
            'Gcard': {
                'xor': {
                    'Type': 'Explicit',
                    'Values': [0, 1]
                }
            },
            'Attribute': {
                'integer': {
                    'Type': 'IntRange',
                    'LowerBoundary': 0,
                    'UpperBoundary': 5
                },
                'float': {
                    'Type': 'FloatRange',
                    'LowerBoundary': 0,
                    'UpperBoundary': 5
                }
            }
        }
        self.initialize_product(self.descr_temp)
        self.constraint_sat_problems = {}
        self.PySAT_solver()
        print(self.seq)
        print('============================================')
        fid = 1
        for x in self.seq:
            if 'Inner_Waffle_Group' in x:
                print('--------------------INNER WAFFLE GROUP-----------------------')

                sat = {
                    x: {
                        'Elems': {},
                        'Constraints': [],
                        'SAT': []
                    }
                }
                for index in range(self.seq.index(x) + 1, len(self.seq)):
                    if ((elem := self.seq[index]).startswith('Constraint_')):
                        constr_md = self.constraints[elem]['Metadata']
                        constr_dict = {
                            'Name': elem,
                            'Parent': fid
                        }
                        print(self.constraints[elem])
                        print(constr_dict)
                        if constr_md['ParentFeature'] not in sat[x]['Elems'].values():
                            sat[x]['Elems'].update({fid: constr_md['ParentFeature']})
                            fid += 1
                        for assign_type in ['Assign', 'Read']:
                            for feature_type in ['Fcard', 'Gcard', 'Value']:
                                for feature in constr_md[assign_type][feature_type]:
                                    if feature not in sat[x]['Elems'].values():
                                        sat[x]['Elems'].update({fid: feature})
                                        fid += 1
                        for op in constr_md['Precedence'].values():
                            print(op)
                print('-------------------------------------------')
                print(sat)