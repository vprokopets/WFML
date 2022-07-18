
class FeatureAnalyzer:
    def __init__(self, api) -> None:
        self.api = api

    def analyze_feature_model(self, stages):
        self.namespace = self.api.namespace
        self.cycles = self.api.cycles
        for stage in stages:
            if stage in self.cycles.keys():
                self.analyze_feature(cycle=self.cycles[stage])
            else:
                self.analyze_feature(tlf=stage)

    def analyze_feature(self, tlf=None, cycle=None):
        temp = {}
        if cycle is not None:
            for feature in cycle:
                for constraint, value in self.namespace[feature]['Constraints'].items():
                    temp.update({f'{feature}_{constraint}': value})
        else:
            temp = self.namespace[tlf]['Constraints']
        self.constraints_sequence_definition(constraints=temp, tlf=tlf, cycle=cycle)

    def constraints_sequence_definition(self, constraints, tlf=None, cycle=None):
        assign_constraints, dependencies = [], []
        for constraint, value in constraints.items():
            if 'prec10' in value['Operations']:
                assign_constraints.append(constraint)
        for assign_constraint in assign_constraints:
            for constraint, value in constraints.items():
                for assign_feature in constraints[assign_constraint]['FeaturesToAssign']:
                    if assign_feature in value['Features'] and [assign_constraint, constraint] not in dependencies:
                        dependencies.append([assign_constraint, constraint])

        cycles, dependent_constraints = self.api.define_sequence_for_deps(dependencies)
        dependent_constraints.reverse()
        if cycles != {}:
            for value in cycles.values():
                first = constraints[value[0]]['Expression']
                second = constraints[value[1]]['Expression']
                rf_first = constraints[value[0]]['RelatedFeature']
                rf_second = constraints[value[1]]['RelatedFeature']
                raise Exception(f'There are cycled constraints: {first} for feature {rf_first} and {second} for feature {rf_second}.\n \
Please rewrite them to avoid cycled dependencies.')
        independent_constraints = []
        for constraint in constraints.keys():
            if constraint not in dependent_constraints:
                independent_constraints.append(constraint)
        res = independent_constraints + dependent_constraints
        if cycle is None:
            self.namespace[tlf]['ConstraintsValidationOrder'] = res
        else:
            for sub_tlf in cycle:
                subres = []
                for feature in res:
                    if sub_tlf in feature:
                        subres.append(int(feature.replace(f'{sub_tlf}_', '')))
                self.namespace[sub_tlf]['ConstraintsValidationOrder'] = subres
        print(f'Success')

    def cardinalities_analysis(self):
        pass

    def type_analysis(self):
        pass
