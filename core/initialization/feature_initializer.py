import logging

from core.auxiliary import cname
from core.initialization.constraint_initializer import ConstraintInitializer

class FeatureInitializer:
    def __init__(self, workspace):
        self.workspace = workspace

        # Every constraint is associated with some feature 
        # TODO:(currently global constraints are not supported)
        self.constraint_initializer = ConstraintInitializer(workspace)

    def parse_feature(self, feature, parent_name=None, parsing_objects='Feature'):
        """
        ! This method is recursive.

        Function to define features.

        INPUTS
        feature (type = feature): feature to define.
        parent_namespace (type = dict): parent feature namespace to fullfill.

        RETURN
        parent_namespace (type = dict): fullfilled parent namespace. Only for not top-level features.
        """
        # Waffle uses the full name with a dot separator to navigate through the hierarchical structure (e.g., A.B.C)
        feature_name = feature.name if parent_name is None else f'{parent_name}.{feature.name}'

        # To assign all constraints associated with a feature
        constraints = []

        # Double cycle due to textX generated class structure
        for child_obj in feature.nested:
            for children in child_obj.child:
                if cname(children) == 'Feature':
                    self.parse_feature(children, feature_name, parsing_objects)
                elif cname(children) == 'Constraint' and parsing_objects == 'Constraint':
                    constraints.append(self.constraint_initializer.parse_constraint(children, feature_name)['ID'])

        if parsing_objects == 'Feature':
            # We separate leaf features that can have attributes and branch features that do not
            # TODO: Define motivation or remove this limitation
            if feature.super is not None and feature.reference is not None:
                raise Exception(f'Super feature and Reference feature could not appear at the same time for {feature_name}')

            # Special handling for Context feature
            if feature_name == 'Context' and feature.fcard not in [None, 1]:
                raise Exception('Context feature is not allowed to have cartinality value other than 1')
            self._initialize_feature(name=feature_name,
                                     fcard=feature.fcard,
                                     gcard=feature.gcard,
                                     value=feature.init,
                                     abstract=feature.abstract,
                                     inheritance=feature.super,
                                     attribute=feature.type,
                                     constraints=None)
        # Add constraints to appropriate feature workspace part
        elif parsing_objects == 'Constraint' and constraints != []:
            self.workspace.update_metadata(feature_name, 'Constraints', constraints)

    def _initialize_feature(self, name, fcard, gcard, value, abstract, inheritance, attribute, constraints):
        mm = self.workspace.features
        self.test_graph = []

        # If initialization starts from not top-level feature, this may prevent absent workspace errors
        # i.e., for A.B it will create a template for feature A that can be updated during appropriate feature configuration
        for level in name.split('.'):
            if level not in mm.keys():
                mm.update({level: {'__self__': {
                    'DeactStandard': False,
                    'ActiveF': True,
                    'ActiveG': True,
                    'Active': True,
                    'Fcard': 1,
                    'Gcard': 'all',
                    'Value': None,
                    'Abstract': None,
                    'Inheritance': None,
                    'Attribute': None,
                    'Constraints': None
                }}})
            mm = mm[level]

        # Update feature attributes with pre-defined values
        mm.update({'__self__': {
            'DeactStandard': False,
            'ActiveF': True,
            'ActiveG': True,
            'Active': True,
            'Fcard': fcard if fcard is not None else 1,
            'Gcard': gcard if gcard is not None else 'all',
            'Value': value,
            'Abstract': abstract,
            'Inheritance': inheritance.replace(':', '') if inheritance is not None else None,
            'Attribute': attribute.replace('->', '') if attribute is not None else None,
            'Constraints': None
        }})

        # Update inheritance dependency list if there is
        if inheritance is not None:
            self.workspace.inheritance.append((name, mm['__self__']['Inheritance']))

        # Later be used to activate fcards (to make appropriate changes in workspace after creating a dependency graph)
        self.workspace.initial_fcards.update({
            name: {
                'MM': mm,
                'Value': fcard
            }
        })
