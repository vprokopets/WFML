import pytest
from core.waffle import Waffle
from json import loads


@pytest.fixture(scope='function')
def get_feature_model():
    def _get_feature_model(model_name: str):
        api = Waffle(True)
        with open(f"./core/examples/{model_name}.wfl", 'r') as model:
            api.initialize_product(model.read())
        return api
    yield _get_feature_model
