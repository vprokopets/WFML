from core.validation.cardinality_validation import CardinalityValidator
from core.validation.constraint_validation import ConstraintValidator


class Validator:
    def __init__(self, workspace, storage):
        self.workspace = workspace
        self.cardinality_validator = CardinalityValidator(workspace)
        self.constraint_validator = ConstraintValidator(workspace, storage)

    def validate_form(self, form_data):

        validation_errors = []
        for field, value in form_data.items():

            # check cardinality form imputs if there is any
            split = field.split('.', 1)
            if split[0] in ['Fcard', 'Gcard']:
                name = split[1]
                field = split[0]
                res, err = self.cardinality_validator.check_cardinality_value(name, value, field)
                if res is False:
                    validation_errors.append((Exception(err, [field]), 'Waffle validation error'))
            else:
                name = field
                field = 'Value'
            if validation_errors != []:
                return validation_errors, 'Cardinality validation error(s)'
            # update workspace if there is no cardinality form errors
            else:
                err = self.workspace.update_metadata(name, field, value)
                if err is not None:
                    validation_errors.append((Exception(err, [field]), 'Waffle validation error'))
                    return validation_errors, 'Value assignment error(s)'

        ret, err_type = self.constraint_validator.validate_constraints()
        if ret is not True:
            validation_errors.append((ret, err_type))
            return validation_errors, 'Constraint validation error(s)'
        return validation_errors, 'No validation errors'
