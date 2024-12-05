from core.waffle import Waffle


class ProductConfigurator:
    def __init__(self, api: Waffle):
        self.api = api
        self.current_step = 0
        tlf = self.api.seq[0]
        self.undefined_features = self.api.get_undefined_features(tlf.split('-')[0])

    def configure(self, variable_value_mapping: dict):
        for feature in self.undefined_features["Value"]:
            metadata = self.api.read_metadata(feature)
            if metadata["__self__"]["Attribute"] == "floatArray":
                self.api.update_metadata(feature, "Value", variable_value_mapping[feature])

        #assert all([self.api.validate_constraints(stage)[0] for stage in self.api.seq]) is True # TODO Bug?

        result = self.api.save_json()

        return result
