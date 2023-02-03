import itertools
from pprint import pprint


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
                for assign_feature in constraints[assign_constraint]['Assign']['Value']:
                    if assign_feature in value['Read']['Value'] and [assign_constraint, constraint] not in dependencies \
                            and assign_constraint != constraint:
                        dependencies.append([assign_constraint, constraint])
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
        combinations = itertools.product(*self.api.requirements.values())
        for iter, comb in enumerate(combinations):
            temp = {}
            for index, constraint in enumerate(comb):
                for feature, value in constraint.items():
                    if feature not in temp.keys():
                        temp.update({feature: {True: [], False: []}})
                    temp[feature][value].append(expressions[index])
                validity = True
                for feature, value in temp.items():
                    check = all(x != [] for x in list(value.values()))
                    if check is True:
                        validity = False
                        if feature not in self.inconsistencies.keys():
                            self.inconsistencies.update({feature: []})
                        features = self.inconsistencies[feature]
                        for x in list(value.values()):
                            features = list(set(features + x))
                        self.inconsistencies.update({feature: features})
                self.validity.update({iter: validity})
        if not any(list(self.validity.values())):
            msg = ''.join(('Constraints cardinalities inconsistencies, please check the following constraints \n',
                           '\n'.join(f'{k}: {v}' for k, v in self.inconsistencies.items())))
            msg = msg.replace('; ', '')
            raise Exception(msg)

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
