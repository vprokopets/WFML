import copy
import logging
from typing import OrderedDict

class FeatureInitializer:
    def __init__(self, api) -> None:
        self.api = api
        self.feature_pattern = {
            'Value': None,
            'Type': None,
            'Fcard': None,
            'Gcard': None,
            'Active': None,
            'Abstract': None,
            'SuperFeature': None,
            'Reference': None,
            'DeepReference': None
        }

        self.constraint_pattern = {
            'RelatedFeature': None,
            'Constraint': None,
            'HigherOperation': None,
            'Operations': [],
            'Features': [],
            'FeaturesToAssign': [],
            'Expression': ''
        }

        self.top_level_pattern = {
            'Features': {},
            'Constraints': {},
            'ConstraintsValidationOrder': OrderedDict()
        }

        self.namespace = {}

    def cname(self, obj):
        """
        Function to return class name of object.

        INPUTS
        obj: object to check.

        RETURN
        (type = string): object`s class name.
        """
        return obj.__class__.__name__

    def initial_type_reference_check(self, reference):
        allowed_types = ['integer', 'float', 'string', 'predefined', 'array', 'integerArray', 'floatArray', 'boolean']
        if reference in allowed_types:
            return reference
        else:
            msg = f'Type {reference} is not allowed to use!\n, \
                Allowed types: {allowed_types}.'
            raise Exception(msg)

    def generate_feature_tmpl(self, feature, full_name):
        feature_tmpl = copy.deepcopy(self.feature_pattern)
        feature_tmpl['Type'] = self.initial_type_reference_check(
            feature.type.rsplit("->")[-1]) if feature.type is not None else None
        feature_tmpl['Fcard'] = {'Original': feature.fcard} if feature.fcard is not None else {'Original': 1}
        feature_tmpl['Gcard'] = {'Original': feature.gcard} if feature.gcard is not None else {'Original': None}
        feature_tmpl['Value'] = {'Original': feature.init} if feature.init is not None else {'Original': None}
        feature_tmpl['Abstract'] = feature.abstract

        super_feature, reference_feature, deepness = self.analyze_super_reference_relations(feature, full_name)
        feature_tmpl['SuperFeature'] = super_feature
        feature_tmpl['Reference'] = reference_feature if deepness is False else None
        feature_tmpl['DeepReference'] = reference_feature if deepness is True else None
        if feature.super is not None and feature.reference is not None:
            raise Exception(f'Super feature and Reference feature could not appear at the same time for {feature.name}')
        return feature_tmpl

    def analyze_super_reference_relations(self, feature, full_name):
        super, reference, deep = None, None, None
        if feature.super is not None:
            super = feature.super.replace(':', '')
            self.super_dependencies.append([full_name.split('.')[0], super])
        if feature.reference is not None:
            if '->>>' in feature.reference:
                deep = True
                reference = feature.reference.replace('->>>', '')
            else:
                deep = False
                reference = feature.reference.replace('->>', '')
            self.reference_dependencies.append([full_name.split('.')[0], reference])
        return super, reference, deep

    def define_feature(self, feature, parent_name=None):
        """
        ! This method is recursive.

        Function to define features.

        INPUTS
        feature (type = feature): feature to define.
        parent_namespace (type = dict): parent feature namespace to fullfill.

        RETURN
        parent_namespace (type = dict): fullfilled parent namespace. Only for not top-level features.
        """
        feature_name = feature.name if parent_name is None else f'{parent_name}.{feature.name}'
        if feature_name not in self.top_level_feature['ConstraintsValidationOrder'].keys():
            self.top_level_feature['ConstraintsValidationOrder'].update({feature_name: None})
        for child in feature.nested:
            for child1 in child.child:
                if self.cname(child1) == 'Feature':
                    self.define_feature(child1, feature_name)
        for child in feature.nested:
            for child1 in child.child:
                if self.cname(child1) == 'Constraint':
                    self.define_constraint(child1, feature_name)

        self.top_level_feature['Features'].update({feature_name: self.generate_feature_tmpl(feature, feature_name)})
        logging.info(f'{"Top-level " if parent_name is None else ""}Feature {feature_name} was defined.')

    def define_constraint(self, constraint, related_feature):
        self.constraints_counter += 1
        pattern = copy.deepcopy(self.constraint_pattern)
        pattern.update({
            'RelatedFeature': related_feature,
            'Constraint': constraint,
        })
        self.top_level_feature['Constraints'].update({
            self.constraints_counter: pattern
        })

    def define_super_relations(self, top_level_feature, feature_name, super_feature_name):
        try:
            tlf_value = self.namespace[super_feature_name]
            if tlf_value['Features'][super_feature_name]['Abstract'] is None:
                raise Exception(f'Reference feature is not abstract: {super_feature_name}')
        except KeyError:
            raise Exception(f'No such super feature exist among top-level features: {super_feature_name}')
        for feature, feature_value in tlf_value['Features'].items():
            inherited_fname = f'{feature_name}.{feature.split(".", 1)[-1]}'
            inh_value = copy.deepcopy(feature_value)
            if inherited_fname not in self.namespace[top_level_feature]['Features'].keys():
                self.namespace[top_level_feature]['Features'].update({inherited_fname: inh_value})
                if inherited_fname not in self.top_level_feature['ConstraintsValidationOrder'].keys():
                    self.top_level_feature['ConstraintsValidationOrder'].update({inherited_fname: None})
        constraints_count = len(list(self.namespace[top_level_feature]['Constraints'].keys()))
        for constraint, constraint_value in tlf_value['Constraints'].items():
            split = constraint_value['RelatedFeature'].split('.')
            split[0] = feature_name
            inh_constraint = copy.deepcopy(self.constraint_pattern)
            inh_constraint.update({
                'RelatedFeature': '.'.join(split),
                'Constraint': constraint_value['Constraint'],
            })
            self.namespace[top_level_feature]['Constraints'].update({constraints_count + constraint: inh_constraint})

    def define_references(self, top_level_feature, feature_name, reference_features):
        for tlf, tlf_value in self.namespace.items():
            if tlf_value['Features'][tlf]['Abstract'] is not None and \
                    tlf_value['Features'][tlf]['SuperFeature'] in reference_features:
                for feature, feature_value in tlf_value['Features'].items():
                    inherited_fname = f'{feature_name}.{feature}'
                    inh_value = copy.deepcopy(feature_value)
                    if feature == tlf:
                        inh_value.update({'Abstract': None})
                    if inherited_fname not in self.namespace[top_level_feature]['Features'].keys():
                        self.namespace[top_level_feature]['Features'].update({inherited_fname: inh_value})
                        if inherited_fname not in self.top_level_feature['ConstraintsValidationOrder'].keys():
                            self.top_level_feature['ConstraintsValidationOrder'].update({inherited_fname: None})
                constraints_count = len(list(self.namespace[top_level_feature]['Constraints'].keys()))
                for constraint, constraint_value in tlf_value['Constraints'].items():
                    inh_constraint = copy.deepcopy(self.constraint_pattern)
                    inh_constraint.update({
                        'RelatedFeature': f'{feature_name}.{constraint_value["RelatedFeature"]}',
                        'Constraint': constraint_value['Constraint'],
                    })
                    self.namespace[top_level_feature]['Constraints'].update({constraints_count + constraint: inh_constraint})

    def initialize_namespace(self, model):
        """
        Calls feature definition function for all features in the model.
        """
        logging.info('Feature definition: Starting.')
        self.namespace = {}
        self.super_dependencies = []
        self.reference_dependencies = []
        for element in model.elements:
            if self.cname(element) == 'Feature':
                self.constraints_counter = 0
                self.top_level_feature = copy.deepcopy(self.top_level_pattern)
                self.define_feature(element)
                self.namespace.update({str(element.name): copy.copy(self.top_level_feature)})
        logging.info('Feature definition: Finished.')

        super_cycles, super_sequence = self.api.define_sequence_for_deps(self.super_dependencies)
        if super_cycles != {}:
            raise Exception(f'There are cycled super relations: {super_cycles}')
        right_parts = []
        for dep in self.super_dependencies:
            right_parts.append(dep[0])
        for feature in copy.copy(super_sequence):
            if feature not in right_parts:
                del super_sequence[super_sequence.index(feature)]

        reference_cycles, reference_sequence = self.api.define_sequence_for_deps(self.reference_dependencies)
        if reference_cycles != {}:
            raise Exception(f'There are cycled reference relations: {reference_cycles}')
        right_parts = []
        for dep in self.reference_dependencies:
            right_parts.append(dep[0])
        for feature in copy.copy(reference_sequence):
            if feature not in right_parts:
                del reference_sequence[reference_sequence.index(feature)]

        logging.info('Feature super relation filling: Starting')
        for tlf in super_sequence:
            for feature, feature_value in self.namespace[tlf]['Features'].copy().items():
                if feature_value['SuperFeature'] is not None:
                    self.define_super_relations(tlf, feature, feature_value['SuperFeature'])
        logging.info('Feature super relation filling: Finished')
        logging.info('Feature reference relation filling: Starting')
        for tlf in reference_sequence:
            for feature, feature_value in self.namespace[tlf]['Features'].copy().items():
                if feature_value['Reference'] is not None:
                    self.define_references(tlf, feature, [feature_value['Reference']])
                elif feature_value['DeepReference'] is not None:
                    deep_references = [feature_value['DeepReference']]
                    end_loop = False
                    while end_loop is False:
                        temp = []
                        end_loop = True
                        for ref in deep_references:
                            for super_dep in self.super_dependencies:
                                if ref == super_dep[1] and super_dep[0] not in deep_references:
                                    end_loop = False
                                    temp.append(super_dep[0])
                        deep_references += temp
                    self.define_references(tlf, feature, deep_references)
        logging.info('Feature reference relation filling: Finished')
        return self.namespace
