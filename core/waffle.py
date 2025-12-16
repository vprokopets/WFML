import json
import logging
from functools import wraps
from pathlib import Path

from textx import metamodel_from_file

from core.dependency_graph import DependencyGraph
from core.initialization.product_initializer import ProductInitializer
from core.storage import Storage
from core.test_generator import ConfigurationLogger
from core.validation.validator import Validator
from core.workspace import Workspace

from core.expressions.array_operations import (
    prec0, prec1, prec2, prec3, prec4, prec5
)
from core.expressions.boolean_operations import (
    prec11, prec12, prec13, prec14, prec15, prec16, prec17,
    prec18, prec19, prec20, prec21, prec22, prec23, prec24
)
from core.expressions.math_operations import (
    prec6, prec7, prec8, prec9, prec10, prec50
)
from core.expressions.terminal_operations import term

TEXTX_CLASSES = [
    prec0, prec1, prec2, prec3, prec4, prec5, prec50, prec6, prec7, prec8,
    prec9, prec10, prec11, prec12, prec13, prec14, prec15, prec16, prec17,
    prec18, prec19, prec20, prec21, prec22, prec23, prec24, term
]

class ProductNotInitializedError(Exception):
    """Custom error for stack trace."""
    pass

def requires_initialization(func):
    @wraps(func)
    def wrapper(self, *args, **kwargs):
        if not self.is_initialized:
            raise ProductNotInitializedError(
                f"Cannot call '{func.__name__}' because the product is not initialized."
            )
        return func(self, *args, **kwargs)
    return wrapper

class Waffle:
    def __init__(self, debug_mode) -> None:
        self.debug_mode = debug_mode
        self.is_initialized = False

    def initialize_product(self, description):
        """
        Performs initial model preprocessing.

        INPUTS
        description: model description from web interface or file.

        """
        self.reset_configurator()

        self.workspace.description = description
        logging.info(f'Processing model: \n{description}')
        grammar_link = Path(__file__).parent / 'grammar.tx'
        mm = metamodel_from_file(file_name=grammar_link,
                                 classes=TEXTX_CLASSES,
                                 autokwd=True)

        # Create and process textX model object from description
        logging.info('Building TextX metamodel...')
        model = mm.model_from_str(description)
        logging.info('Building TextX metamodel done')
        logging.info('Building Waffle metamodel...')
        self._initializer.initialize_product(model)
        logging.info('Building Waffle metamodel done')

        self.configuration_logger.save_feature_model(description)
        # To avoid adding abstract features to metagraph
        self.workspace.disable_abstract_features()

        self._initializer.build_metagraph()

        self.dependency_graph = DependencyGraph()
        # For element placing using different compositions (e.g., hierarchical and random)
        self.dependency_graph.define_graph_layout(self.storage.dependencies)

        # Must be done after dependency graph definicion to avoid missing or multiple graph elements
        # i.e., creating workspace for features with cardinality >1, disabling features with cardinality ==0, etc.
        # (since cardinality is a feature property, not self-sufficient graph element)
        self.workspace.activate_fcards()

        # TODO whether this method is required?? It's used just for representation
        self._initializer.group_constraints()

        self.workspace.register_dependency_graph_layout(self.dependency_graph.get_graph_state())
        self.workspace.save_constraint_data()

        self.is_initialized = True
        logging.info('Initial Waffle configuration is done')
        print('-------------------------------')

    @requires_initialization
    def validate_form(self, form_label, form_meta, form_data):
        """
        Validate inputs and respective constraints.

        RETURN
        validation_errors (type = list): an array of errors occured
        error_state (type = string): textual state representation (e.g., no errors, cardinality validation error, etc).
        """

        logging.info(f'Validating form {form_data}')
        self.workspace.current_stage = form_meta
        logging.info(f'Current stage: {self.workspace.current_stage}')

        validation_errors, error_state = self._validator.validate_form(form_data)

        self.configuration_logger.save_current_step(form_label, form_data, validation_errors)
        return validation_errors, error_state

    @requires_initialization
    def save_json(self):
        """
        Prepare and save final result.

        RETURN
        res (type = dict): final result
        """

        product = self.workspace.get_product(self.workspace.features, {})

        # Use Pathlib for better path handling
        output_path = Path('./core/output/configuration.json')
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(product, f, ensure_ascii=False, indent=4)

        return product

    def reset_configurator(self):
        """
        Reset all variables for new configuration.

        RETURN
        None
        """
        self.is_initialized = False
        self._initialize_main_components()

    def _initialize_main_components(self):
        """
        Initialize main Waffle modules.

        RETURN
        None
        """
        self.workspace = Workspace(self)
        self.storage = Storage(self.workspace)

        self._initializer = ProductInitializer(self.workspace, self.storage)
        self._validator = Validator(self.workspace, self.storage)

        self.configuration_logger = ConfigurationLogger()
