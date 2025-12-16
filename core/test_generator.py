import json


class ConfigurationLogger:
    def __init__(self):
        self.feature_model = None
        self.configuration_sequence = {}

    def save_feature_model(self, feature_model):
        self.feature_model = feature_model

    def save_current_step(self, step, cleaned_data, validation_errors):
        errors = []
        for res in validation_errors:
            if res is not True:
                msg, elems = res[0].args
                errors.append({'msg': msg, 'elems': elems})
        self.configuration_sequence.update({step: {'data': cleaned_data, 'errors': errors}})
        with open('./core/output/test.json', 'w', encoding='utf-8') as f:
            json.dump({'feature_model': self.feature_model, 'configuration': self.configuration_sequence},
                      f,
                      ensure_ascii=False,
                      indent=4)
