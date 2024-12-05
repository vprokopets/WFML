import pytest
from core.product_configurator import ProductConfigurator


class TestProductConfiguration:
    """
    Test whether selected feature models are configured correctly.
    """
    def test_array(self, get_feature_model):
        api = get_feature_model("array")
        product_configurator = ProductConfigurator(api)
        variable_value_mapping = {"A.Weights": "[1, 2, 3]"}
        configuration = product_configurator.configure(variable_value_mapping)

        assert configuration == {'A': {'Weights': '[1, 2]'}}

