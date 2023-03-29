import collections
import itertools


class FeatureAnalyzer:
    def __init__(self, api) -> None:
        self.api = api

    def analyze_feature_model(self, stages):
        """
        The function contains calls to perform several analyses of the feature model.

        INPUTS
        stages (type = list): list of top-level features for analysis.

        """
        self.namespace = self.api.namespace
        self.cardinalities_analysis()
        self.type_analysis()
        self.cycles = self.api.cycles
        for stage in stages:
            if stage in self.cycles.keys():
                self.analyze_feature(cycle=self.cycles[stage])
            else:
                self.analyze_feature(tlf=stage)

    def analyze_feature(self, tlf=None, cycle=None):
        """
        Preprocessing function for constraints sequence definition of some top-level feature

        INPUTS
        ! Please note that only one of the inputs can be used.
        tlf (type = string): name of the top-level feature.
        cycle (type = list): list of all top-level features in the cycle.

        """
        temp = {}
        if cycle is not None:
            for feature in cycle:
                for constraint, value in self.namespace[feature]['Constraints'].items():
                    temp.update({f'{feature}_{constraint}': value})
        else:
            temp = self.namespace[tlf]['Constraints']
        self.constraints_sequence_definition(constraints=temp, tlf=tlf, cycle=cycle)

    def constraints_sequence_definition(self, constraints, tlf=None, cycle=None):
        """
        Function to define the sequence of top-level feature constraints validation.

        INPUTS
        ! Please note that only one of the inputs can be used.
        constraints (type = dict): dict that contains constraint objects.
        tlf (type = string): name of the top-level feature.
        cycle (type = list): list of all top-level features in the cycle.

        """
        assign_constraints, dependencies = [], []
        for constraint, value in constraints.items():
            if 'prec10' in value['Operations']:
                assign_constraints.append(constraint)
        for assign_constraint in assign_constraints:
            for constraint, value in constraints.items():
                for assign_type in ['Fcard', 'Gcard', 'Value']:
                    for assign_feature in constraints[assign_constraint]['Assign'][assign_type]:
                        for read_type in ['Fcard', 'Gcard', 'Value']:
                            for read_feature in value['Read'][read_type]:
                                if (assign_feature == read_feature or f'{assign_feature}.' in read_feature) and [assign_constraint, constraint] not in dependencies \
                                        and assign_constraint != constraint:
                                    print(f'Assign: {assign_feature} / Read: {read_feature} / {constraints[assign_constraint]["Assign"]} / {value["Read"]}')
                                    dependencies.append([assign_constraint, constraint])
        print(f'Dependencies: {dependencies}')
        cycles, dependent_constraints = self.api.define_sequence_for_deps(dependencies)
        dependent_constraints.reverse()
        if cycles != {}:
            for value in cycles.values():
                first = constraints[value[0]]['Expression']
                second = constraints[value[1]]['Expression']
                rf_first = constraints[value[0]]['RelatedFeature']
                rf_second = constraints[value[1]]['RelatedFeature']
                msg = '\n'.join(('There are cycled constraints:',
                                 f'{first} for feature {rf_first} and {second} for feature {rf_second}.',
                                 'Please rewrite them to avoid cycled dependencies.'))
                raise Exception(msg)
        independent_constraints = []
        for constraint in constraints.keys():
            if constraint not in dependent_constraints:
                independent_constraints.append(constraint)
        if cycle is None:
            self.namespace[tlf]['ConstraintsValidationOrder'] = dependent_constraints
            self.namespace[tlf]['IndependentConstraints'] = independent_constraints
        else:
            for sub_tlf in cycle:
                subres = []
                for feature in dependent_constraints:
                    if sub_tlf in feature:
                        subres.append(int(feature.replace(f'{sub_tlf}_', '')))
                self.namespace[sub_tlf]['ConstraintsValidationOrder'] = subres
                for feature in independent_constraints:
                    if sub_tlf in feature:
                        subres.append(int(feature.replace(f'{sub_tlf}_', '')))
                self.namespace[sub_tlf]['IndependentConstraints'] = subres

    def cardinalities_analysis(self):
        """
        Function to check the consistency of feature cardinalities.

        """
        self.validity = {}
        self.inconsistencies = {}
        expressions = list(self.api.requirements.keys())
        if len(expressions) == 0:
            return
        single = {}
        multi = {}
        for expr, values in self.api.requirements.items():
            if len(values) == 1:
                for dict_obj in values:
                    for k, v in dict_obj.items():
                        if k in single.keys() and v != single[k]['Value']:
                            msg = ''.join(('Constraints cardinalities mismatch. \n',
                                           f'Please check expressions on feature {k} for constraints: \n',
                                           '\n'f'{single[k]["Expr"]} and {expr}'))
                            msg = msg.replace('; ', '')
                            raise Exception(msg)
                        single.update({k: {'Value': v, 'Expr': expr}})
        false_obj = []
        for expr, values in self.api.requirements.items():
            if len(values) > 1:
                added = False
                for dict_obj in values:
                    add = True
                    for k, v in dict_obj.items():
                        if k in single.keys() and v != single[k]['Value']:
                            add = False
                            false_obj.append(k)
                    if add is True:
                        added = True
                        if expr not in multi.keys():
                            multi.update({expr: []})
                        multi[expr].append(dict_obj)
                if added is False:
                    msg = ''.join(('Constraints cardinalities mismatch. \n',
                                   f'Please check all expressions on feature {k} for constraints: \n',
                                   '\n'f'{single[k]["Expr"]} and {expr}'))
                    msg = msg.replace('; ', '')
                    raise Exception(msg)
        combinations = itertools.product(*multi.values())
        success = False
        for iter, comb in enumerate(combinations):
            if iter % 500 == 0:
                print(iter)
            check = self.merge_dicts(comb)
            if check is True:
                success = True
                break
        if success is False:
            msg = ''.join(('Constraints cardinalities mismatch. \n',
                           f'Please check all expressions on feature {check}'))
            msg = msg.replace('; ', '')
            raise Exception(msg)

    def merge_dicts(self, dicts):
        res = collections.defaultdict(list)
        for d in dicts:
            for k, v in d.items():
                if len(res[k]) == 1 and v not in res[k]:
                    return k
                res[k].append(v)
        return True

    def type_analysis(self):
        """
        Function to check the consistency of feature types.

        """
        for tlf in self.namespace.keys():
            for feature, value in self.namespace[tlf]['Features'].items():
                if value['Type'] == 'predefined' and self.namespace[tlf]['Features'][tlf]['Abstract'] is None:
                    check = self.search_for_constraint_assignment(feature)
                    if check is False:
                        msg = ''.join((f'Feature {feature} is predefined type ',
                                      'but there are no constraints that assign any value to this feature.'))
                        raise Exception(msg)

    def search_for_constraint_assignment(self, feature):
        """
        Function to check the presence of some feature in any assignment constraint.

        INPUTS
        feature (type = string): feature name.

        RETURN
        ret (type = bool): the result of the check
        """
        ret = False
        for tlf in self.namespace.values():
            for constraint in tlf['Constraints'].values():
                if feature in constraint['Assign']['Value']:
                    ret = True
        return ret
