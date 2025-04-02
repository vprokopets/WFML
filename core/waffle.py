import json
import logging

from os.path import join, dirname
from textx import metamodel_from_file

from core.dependency_graph import DependencyGraph
from core.workspace import Workspace
from core.storage import Storage
from core.initialization.product_initializer import ProductInitializer
from core.validation.validator import Validator
from core.expressions.array_operations import prec0, prec1, prec2, prec3, prec4, prec5
from core.expressions.boolean_operations import prec11, prec12, prec13, prec14, prec15, prec16, prec17, prec18, prec19, prec20
from core.expressions.boolean_operations import prec21, prec22, prec23, prec24
from core.expressions.math_operations import prec10, prec50, prec6, prec7, prec8, prec9
from core.expressions.terminal_operations import term

class Waffle:
    def __init__(self, debug_mode) -> None:
        self.debug_mode = debug_mode
        self.reset()
        self.workspace = Workspace(self)
        self.storage = Storage(self.workspace)

        self.initializer = ProductInitializer(self.workspace, self.storage)
        self.validator = Validator(self.workspace, self.storage)

    def reset(self):
        self.prec_bool = ['prec23', 'prec22', 'prec21', 'prec20', 'prec19', 'prec18', 'prec14', 'prec11', 'prec0', 'term']
        self.metamodel, self.stage_snap, self.last_snap = {}, {}, {}
        self.initial_fcards, self.groups = {}, {}
        self.features_to_configure = {}
        self.configuration_history = {}
        self.group_constraints = {}
        self.step_status = {}

        self.inheritance = []
        self.metagraph = []

        self.id_counter = 0
        self.card_boundaries = {
            '*': [(0, 1e6)],
            '+': [(1, 1e6)],
            '?': [(0, 1)],
            'or': [(1, 1e6)],
            'xor': [(1, 1)]
        }
        self.constraints = {}

    def validate_form(self, form_label, form_data):
        self.workspace.current_stage = form_label

        validation_errors, error_type = self.validator.validate_form(form_data)
        # TODO validation results logging
        return validation_errors, error_type

    def get_next_constraints(self, step):
        return self.workspace.get_next_constraints(step)

    def register_skipped_step(self, step):
        # TODO update logic or remove
        self.workspace.update_metadata(step)

    def save_json(self):
        """
        Prepare and save final result.

        RETURN
        res (type = dict): final result
        """

        self.feature_product = self.workspace.get_product(self.workspace.features, {})
        logging.info('Final result was successfully created.')
        logging.debug(f'Final Model {self.feature_product}')
        with open('./core/output/configuration.json', 'w', encoding='utf-8') as f:
            json.dump(self.feature_product, f, ensure_ascii=False, indent=4)

        # TODO: Pickling WFML for dynamicity
        # self.pickle_wfml_data()
        return self.feature_product

    def initialize_product(self, description):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        """
        self.reset()
        self.workspace.description = description
        # Read language grammar and create textX metamodel object from it.
        grammar_link = join(dirname(__file__), 'grammar.tx')
        mm = metamodel_from_file(file_name=grammar_link,
                                 classes=[prec0, prec1, prec2, prec3,
                                          prec4, prec5, prec50, prec6, prec7, prec8,
                                          prec9, prec10, prec11, prec12, prec13,
                                          prec14, prec15, prec16, prec17,
                                          prec18, prec19, prec20, prec21, prec22, prec23, prec24, term],
                                 autokwd=True)

        # create and process textX model object from description
        model = mm.model_from_str(description)
        self.initializer.initialize_product(model)

        # to avoid adding abstract features to metagraph
        self.workspace.disable_abstract_features()

        self.initializer.build_metagraph()

        self.dependency_graph = DependencyGraph()
        # for element placing using different compositions (e.g., hierarchical and random)
        self.dependency_graph.define_graph_layout(self.storage.dependencies)

        # must be done after dependency graph definicion to avoid missing or multiple graph elements
        # i.e., creating workspace for features with cardinality >1, disabling features with cardinality ==0, etc.
        # (since cardinality is a feature property, not self-sufficient graph element)
        self.workspace.activate_fcards()

        # TODO whether this method is required?? It's used just for representation
        self.initializer.group_constraints()

        self.workspace.register_dependency_graph_layout(self.dependency_graph.get_graph_state())
