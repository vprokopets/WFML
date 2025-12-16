import copy
import logging
import mimetypes
import json
import io
import pstats

from collections import OrderedDict
from core.waffle import Waffle
from django import forms
from django.http.response import HttpResponse
from django.shortcuts import redirect, render
from formtools.wizard.views import CookieWizardView
from django.core.exceptions import NON_FIELD_ERRORS, ValidationError

# profiling library
import cProfile

debug_mode = False
debug_logger = False
profiling = False

if debug_logger is True:
    logging.basicConfig(format='%(asctime)s - %(levelname)s - %(pathname)s:%(lineno)d - %(funcName)s(): %(message)s',
                        level=logging.DEBUG,
                        datefmt='%m/%d/%Y %I:%M:%S %p')
else:
    logging.basicConfig(format='%(asctime)s - %(levelname)s - %(message)s',
                        level=logging.INFO,
                        datefmt='%m/%d/%Y %I:%M:%S %p')


class WizardStepForm(forms.Form):
    """
    Form that is used to construct and validate each wizard step.
    """

    def add_error(self, field, error):
        """
        Update the content of `self._errors`.

        The `field` argument is the name of the field to which the errors
        should be added. If it's None, treat the errors as NON_FIELD_ERRORS.

        The `error` argument can be a single error, a list of errors, or a
        dictionary that maps field names to lists of errors. An "error" can be
        either a simple string or an instance of ValidationError with its
        message attribute set and a "list or dictionary" can be an actual
        `list` or `dict` or an instance of ValidationError with its
        `error_list` or `error_dict` attribute set.

        If `error` is a dictionary, the `field` argument *must* be None and
        errors will be added to the fields that correspond to the keys of the
        dictionary.
        """
        if not isinstance(error, ValidationError):
            # Normalize to ValidationError and let its constructor
            # do the hard work of making sense of the input.
            error = ValidationError(error)

        if hasattr(error, "error_dict"):
            if field is not None:
                raise TypeError(
                    "The argument `field` must be `None` when the `error` "
                    "argument contains errors for multiple fields."
                )
            else:
                error = error.error_dict
        else:
            error = {field or NON_FIELD_ERRORS: error.error_list}
        for field, error_list in error.items():
            if field not in self.errors:
                if field != NON_FIELD_ERRORS and field not in self.fields:
                    raise ValueError(
                        "'%s' has no field named '%s'."
                        % (self.__class__.__name__, field)
                    )
                if field == NON_FIELD_ERRORS:
                    self._errors[field] = self.error_class(
                        error_class="nonfield", renderer=self.renderer
                    )
                else:
                    self._errors[field] = self.error_class(renderer=self.renderer)
            self._errors[field].extend(error_list)
            if hasattr(self, 'cleaned_data') and field in self.cleaned_data:
                del self.cleaned_data[field]

    def clean(self):
        """
        Hook for doing any extra form-wide cleaning after Field.clean() has been
        called on every field. Any ValidationError raised by this method will
        not be associated with a particular field; it will have a special-case
        association with the field named '__all__'.
        """
        logging.debug('CLEAN FUNCTION CALL')
        return self.cleaned_data

    def is_valid(self):
        global waffle_api
        self.api = waffle_api
        logging.debug('VALIDATION FUNCTION CALL')
        self.validate()
        """Return True if the form has no errors, or False otherwise."""
        return self.is_bound and not self.errors

    def querydict_to_dict(self, query_dict):
        data = {}
        for key in query_dict.keys():
            v = query_dict.getlist(key)
            if len(v) == 1:
                v = v[0]
            data[key] = v
        return data

    def parse_form_manually(self):
        self.manually_cleaned_data = {}
        input_data = {}
        raw_data = self.querydict_to_dict(copy.deepcopy(self.data))
        for k, v in raw_data.items():
            if (k.startswith((prefix := f'{self.prefix}-'))):
                logging.info(f'Parsing input form {k} with value {v}')
                input_data.update({k.split(prefix)[-1]: v})
        logging.debug(f'Input for manual processing {input_data}')
        for k, v in input_data.items():
            if k.startswith('Fcard.') or k.startswith('Gcard.'):
                if isinstance(v, list):
                    for index, value in enumerate(v):
                        try:
                            v[index] = int(value)
                        except ValueError:
                            pass
                else:
                    try:
                        v = int(v)
                    except ValueError:
                        pass
            else:
                attr_type = self.api.workspace.read_feature_data(k, 'Attribute')
                logging.debug(f'Attribute type for field {k}: {attr_type}')
                if any([x in attr_type for x in ['array', 'Array']]):
                    v = v.replace(' ', '').split(',')
                    if attr_type == 'floatArray':
                        v = [float(x) for x in v]
                    elif attr_type == 'integerArray':
                        v = [int(x) for x in v]
                elif attr_type == 'array':
                    v = v.replace(' ', '').split(',')
                elif attr_type == 'integer':
                    v = int(v)
                elif attr_type == 'float':
                    v = float(v)
                elif attr_type == 'boolean':
                    if v == 'True':
                        v = True
                    elif v == 'False':
                        v = False

            self.manually_cleaned_data.update({k: v})

    def validate(self):
        """
        Function to validate wizard step form.

        RETURN
        cd (type = dict): cleaned data, that was printed to form fields.
        """
        # TODO Update logging message
        # logging.info(f'Validating form: {self.__dict__}. ')
        if profiling is True:
            ob = cProfile.Profile()
            ob.enable()

        self.parse_form_manually()
        cd = copy.deepcopy(self.manually_cleaned_data)
        logging.debug(f'Label: {self.label}')
        logging.debug(f'Cleaned Data: {cd}')
        validation_errors, error_type = self.api.validate_form(self.stage_step, self.meta, cd)
        self.display_validation_feedback(validation_errors, error_type)

        if profiling is True:
            ob.disable()
            sec = io.StringIO()
            sortby = pstats.SortKey.CUMULATIVE
            ps = pstats.Stats(ob, stream=sec).sort_stats(sortby)
            ps.print_stats()

            logging.debug(sec.getvalue())
        return cd

    def display_validation_feedback(self, validation_errors, error_type):
        for res in validation_errors:
            if res is not True:
                fields = self.fields.keys()
                msg, elems = res[0].args
                self.error_md = self.api.workspace.constr_err_md
                self.constr_md = res[2]
                if not any([elem in fields or f'Fcard.{elem}' in fields or f'Gcard.{elem}' in fields for elem in elems]):
                    # TODO check naming bug with _0 index in the name suffix
                    self.add_error(None, f'{error_type}: {msg}')
                else:
                    for elem in elems:
                        attr_type = self.api.workspace.read_feature_data(elem, 'Attribute')
                        for field in self.fields.keys():
                            if attr_type != 'predefined' and (elem == field or f'Fcard.{elem}' == field or f'Gcard.{elem}' == field):
                                self.add_error(field, f'{error_type}: {msg}')
                self.api.storage.restore_stage_snap()


class ModelInputForm(forms.Form):
    """
    Initial form that is used for model input.
    """

    initial_text = ''
    model_field = forms.CharField(widget=forms.Textarea(attrs={'id': 'textarea'}), initial=initial_text)

class WizardClass(CookieWizardView):

    def done(self, form_list, **kwargs):
        """
        ! This method is automatically called after the last step of wizard was successfully validated.

        RETURN
        redirection to final page.
        """
        feature_product = self.api.save_json()
        logging.info(f'! Final result: {feature_product}')
        self.update_configuration_metadata(feature_product)
        return render(self.request, 'done.html', self.configuration_metadata)

    def get_form(self, step=None, data=None, files=None):
        """
        ! This method is automatically called after the previous step of wizard was successfully validated.

        Method to construct form for current wizard step.

        RETURN
        form with all required fields.
        """

        # Create form object.
        if step is None:
            step = self.steps.current
        self.step_number = step
        self.form = super(WizardClass, self).get_form(step, data, files)
        try:
            self.configuration_sequence
        except AttributeError:
            self.configuration_sequence = self.api.storage.test_sequence
        self.current_step = self.configuration_sequence[int(step)]
        logging.info(f'Wizard step {step} | {self.current_step}.')

        self.form.stages_number = len(self.configuration_sequence)
        self.form.stage_step = int(self.step_number)
        constr = []
        for constraint in self.current_step['constraints']:
            constr.append(self.api.workspace.get_constraint_expression(constraint).replace('[', '').replace(']', ''))
        label = f'{self.current_step["features"]}'
        sublabel = f'Constraints to validate: {constr}'
        # Fill form label and head.
        self.form.meta = self.current_step
        self.form.label = label
        self.form.sublabel = sublabel
        self.form.head = ''
        self.form.step_id = id(self)

        self.construct_step_form(self.current_step, files)
        # TODO update graph
        # if self.form.fields != {}:
        #     self.api.workspace.change_dependency_graph_state(self.current_step, 'In Progress')
        # else:
        #     self.api.workspace.change_dependency_graph_state(self.current_step, 'Skipped')
        # TODO update graph state call
        self.form.graph_data = json.dumps(self.api.workspace.dependency_graph_data)

        return self.form

    def update_configuration_metadata(self, feature_product):

        self.form.configuration_history_view = json.dumps(self.api.workspace.configuration_history, indent=4)
        self.form.collapsable_view = list(self.api.workspace.configuration_history.keys())
        self.form.metadata_view = json.dumps(self.api.workspace.features, indent=4)
        self.form.configuration_sequence_view = list(self.api.storage.configuration_sequence)
        self.form.feature_product = json.dumps(feature_product, indent=4)
        self.form.constraint_metadata = json.dumps(self.api.workspace.constraint_metadata, indent=4)
        self.form.constraint_groups = json.dumps(self.api.storage.constraint_groups_representation, indent=4)
        self.form.constraint_groups_full_data = json.dumps(self.api.storage.constraint_groups, indent=4)
        self.configuration_metadata = {
            'history': self.form.configuration_history_view,
            'history_selected': {},
            'collapsable': self.form.collapsable_view,
            'metadata': self.form.metadata_view,
            'metadata_selected': {},
            'selected_feature': None,
            'configuration_sequence': self.form.configuration_sequence_view,
            'feature_product': self.form.feature_product,
            'constraint_metadata': self.form.constraint_metadata,
            'constraint_groups': self.form.constraint_groups,
            'constraint_groups_full_data': self.form.constraint_groups_full_data
        }

    def construct_step_form(self, step_id, files):
        """
        Function to define a fields a wizard form.

        INPUTS
        tlf (type = string): name of top-level feature.
        """
        logging.info(f'Preparing form for {step_id}...')
        form_data = None
        tlf_involved = []
        features_involved = []
        # TODO cycle handling
        # cycles = api.cycles
        cycles = {}
        # If step contains cycle, then get all cycle items and perform field initialization for all of them.
        # if self.current_step in cycles.keys():
        #     for element in (cycle_elems := cycles[self.current_step]):
        #         tlf_involved.append(self.api.workspace.get_feature_base_name(element.split('-')[0].split('.')[0]))
        #         features_involved.append(element)
        #     logging.debug(f'Making cycle form group {self.current_step} || {cycle_elems}')
        # elif 'Waffle_Constraint_Group_' in self.current_step:
        #     for element in (group_elems := self.api.storage.constraint_groups[self.current_step]):
        #         tlf_involved.append(self.api.workspace.get_feature_base_name(element.split('-')[0].split('.')[0]))
        #         features_involved.append(element)
        #     logging.debug(f'Making form group {self.current_step} || {group_elems}')
        # else:
        #     tlf_involved.append(self.api.workspace.get_feature_base_name(step_id.split('-')[0].split('.')[0]))
        #     features_involved.append(step_id)
        #     logging.debug(f'Making single form {self.current_step}')

        for element in (group_elems := step_id['features']):
            tlf_involved.append(self.api.workspace.get_feature_base_name(element.split('-')[0].split('.')[0]))
            features_involved.append(element)
        logging.debug(f'Making form group {self.current_step} || {group_elems}')
        if self.step_number not in self.api.storage.stage_snap.keys():
            form_data = {'Fcard': [], 'Gcard': [], 'Value': []}
            for tlf in tlf_involved:
                unconfigured_features = self.api.workspace.get_unconfigured_features(tlf)
                for ftype, features in unconfigured_features.items():
                    for feature in features:
                        if feature not in form_data[ftype]:
                            form_data[ftype].append(feature)
            self.api.storage.save_stage_snap(self.step_number, form_data)
            logging.debug(f'Initializing form for {self.step_number}')
        else:
            form_data = self.api.storage.stage_snap[self.step_number]['Fields']
            if files is None:
                logging.debug(f'Updating form for {self.step_number}')
                self.api.storage.restore_stage_snap(self.step_number)
                logging.debug('Namespace was restored')
                self.form.full_clean()
                logging.debug(f'Cleaning form {self.step_number}')
                form_data = {'Fcard': [], 'Gcard': [], 'Value': []}
                for tlf in tlf_involved:
                    unconfigured_features = self.api.workspace.get_unconfigured_features(tlf)
                    for ftype, features in unconfigured_features.items():
                        for feature in features:
                            if feature not in form_data[ftype]:
                                form_data[ftype].append(feature)
                self.api.storage.save_stage_snap(self.step_number, form_data)
        if form_data is None:
            return

        logging.debug(f'DATA {form_data} | tlf {tlf_involved} | step {self.step_number}')
        logging.debug(f'Features involved: {features_involved}')
        data_filtered = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        for feature_type, features in form_data.items():
            for feature_name in features:
                if f'{self.api.workspace.get_feature_base_name(feature_name)}-{feature_type}' in features_involved:
                    data_filtered[feature_type].append(feature_name)
        logging.debug(f'Filtered features: {data_filtered}')

        self.construct_feature_cardinality_forms(data_filtered['Fcard'])
        self.construct_group_cardinality_forms(data_filtered['Gcard'])
        self.construct_attribute_value_forms(data_filtered['Value'])

        if 'Waffle_Constraint_Group_' in self.current_step:
            self.form.head = 'Combined step for constraint feature group'
        elif len(data_filtered['Value']) > 0:
            self.form.head = 'Features to configure: '
        elif len(data_filtered['Fcard']) > 0 or len(data_filtered['Gcard']) > 0:
            self.form.head = 'Cardinalities to configure: '
        else:
            self.form.head = 'Empty step'

        self.form.next_constraints = step_id['constraints']
        self.update_configuration_metadata('')
        self.form.configuration_metadata = self.configuration_metadata
        logging.info(f"Finish preparing form {self.current_step}")

    def construct_feature_cardinality_forms(self, feature_cardinalities):
        """
        Function to define a feature cardinality fields a wizard form.

        INPUTS
        feature_cardinalities (type = dict): dict with all feature cardinalities.
        """
        for fcard in feature_cardinalities:
            value = self.api.workspace.read_feature_data(fcard, 'Fcard')
            allowed = None
            if value == '*':
                allowed = '0..inf'
            elif value == '+':
                allowed = '1..inf'
            elif value == '?':
                allowed = '0 or 1'
            else:
                allowed = value
            self.form.fields[f'Fcard.{fcard}'] = forms.IntegerField(
                label=f'Feature Cardinality for feature {fcard}. Allowed values: {allowed}'
            )

    def construct_group_cardinality_forms(self, group_cardinalities):
        """
        Function to define a group cardinality fields a wizard form.

        INPUTS
        group_cardinalities (type = dict): dict with all group cardinalities.
        """
        # Create fields for each gcard record.
        for gcard in group_cardinalities:
            # Create appropriate fields in form.
            value = self.api.workspace.read_feature_data(gcard, 'Gcard')
            options_full = self.api.workspace.get_feature_childrens(gcard)
            options = [x.rsplit('.', 1)[-1] for x in options_full]
            choises_list = []
            for option in options:
                choises_list.append((option, option))
            # Ignore fields are used to ensure correctness of form.
            # CookieWizardView validates each form twice: right after their filling and in the end.

            if value == 'xor':
                self.form.fields[f'Gcard.{gcard}'] = forms.ChoiceField(label=f'Gcard.{gcard}', choices=choises_list,
                                                                       widget=forms.RadioSelect)
            else:
                self.form.fields[f'Gcard.{gcard}'] = forms.MultipleChoiceField(label=f'Gcard.{gcard}', choices=choises_list,
                                                                               widget=forms.CheckboxSelectMultiple)
            # Fix for lowercase label
            self.form.fields[f'Gcard.{gcard}'].label = (f'Group cardinality for feature {gcard} '
                                                        f'(Type: {value if value in ['xor', 'or'] else f'or with interval(s) {value}'})')

    def construct_attribute_value_forms(self, attribute_values):
        for feature in attribute_values:
            feature_type = self.api.workspace.read_feature_data(feature, 'Attribute')
            # Check if this field is allowed by chosen group cardinality.
            if feature_type == 'integer':
                self.form.fields[feature] = forms.IntegerField(label=f'{feature}  (Type: {feature_type})')
            elif feature_type == 'float':
                self.form.fields[feature] = forms.FloatField(label=f'{feature} (Type: {feature_type})')
            elif feature_type == 'string' or \
                    feature_type == 'array' or \
                    feature_type == 'integerArray' or \
                    feature_type == 'floatArray':
                self.form.fields[feature] = forms.CharField(label=f'{feature} (Type: {feature_type})')
            elif feature_type == 'boolean':
                choises_list = []
                for v in [True, False]:
                    choises_list.append((v, v))
                self.form.fields[feature] = forms.ChoiceField(label=f'{feature} (Type: {feature_type})',
                                                              choices=choises_list,
                                                              widget=forms.RadioSelect)
            # Sort fields by names. This will group generated fields.
            self.form.fields = OrderedDict(sorted(self.form.fields.items()))

    def process_step(self, form):
        """
        This method is used to postprocess the form data. By default, it
        returns the raw `form.data` dictionary.
        """
        # form.validate()
        logging.debug('PROCESS STEP FUNCTION CALL')
        return self.get_form_step_data(form)

    def get(self, request, *args, **kwargs):
        """
        This method handles GET requests.

        If a GET request reaches this point, the wizard assumes that the user
        just starts at the first step or wants to restart the process.
        The data of the wizard will be reset before rendering the first step
        """
        self.storage.reset()

        # reset the current step to the first step.
        self.storage.current_step = self.steps.first
        first_step_form = self.get_form()
        if first_step_form.fields != {}:
            return self.render(self.get_form())
        else:
            return self.render_next_step(first_step_form)

    def render_next_step(self, form, **kwargs):
        """
        This method gets called when the next step/form should be rendered.
        `form` contains the last/current form.
        """
        # get the form instance based on the data from the storage backend
        # (if available).
        res = False
        skip = True
        # TODO update graph
        # self.api.workspace.change_dependency_graph_state(self.current_step, 'Configured')
        while res is False:
            logging.info(f'Rendering next step {self.steps.next}.')
            next_step = self.steps.next
            new_form = self.get_form(
                next_step,
                data=self.storage.get_step_data(next_step),
                files=self.storage.get_step_files(next_step),
            )
            if new_form.fields != {} or skip is False or 'Waffle_Constraint_Group_' in self.api.storage.test_sequence[int(next_step)]:
                res = True
            else:
                new_form.is_valid()
                if next_step == self.steps.last:
                    return self.done(form_list=[])

            # change the stored current step
            self.storage.current_step = next_step
        logging.info(f'STEP {next_step} | {id(self)}')
        return self.render(new_form, **kwargs)

    def render_done(self, form, **kwargs):
        """
        This method gets called when all forms passed. The method should also
        re-validate all steps to prevent manipulation. If any form fails to
        validate, `render_revalidation_failure` should get called.
        If everything is fine call `done`.
        """
        final_forms = OrderedDict()
        done_response = self.done(list(final_forms.values()), form_dict=final_forms, **kwargs)
        self.storage.reset()
        return done_response

def initial_page(request, *args, **kwargs):
    """
    ! This method is automatically called to render initial page (GET request)
    or to process filled ModelInputForm and create wizard (POST request).

    RETURN
    initial page (GET)
    redirect to wizard (POST)
    """
    if request.method == 'POST':
        # Create a form instance and populate it with data from the request (binding):
        form = ModelInputForm(request.POST)
        if form.is_valid():
            global factory_forms, waffle_api
            model = form.cleaned_data['model_field']
            request.session['feature_model'] = model
            waffle_api = Waffle(debug_mode)
            waffle_api.initialize_product(model)
            factory_forms = []
            for _ in waffle_api.storage.test_sequence:
                factory_forms.append(WizardStepForm)
            return redirect('factory_wizard')

    elif request.method == 'GET':
        form = ModelInputForm()
        return render(request, 'initial.html', {
            'form': form,
        })

def factory_wizard(request, *args, **kwargs):
    """
    This method constructs wizard according with the number of steps, defined in model.

    RETURN
    wizard
    """
    if request.method == 'POST' and 'mybtn2' in request.POST.keys():
        # res = api.save_json()
        logging.info('! Product configuration was not finished. You can always continue from this place.')

        return render(request, 'done.html', {
            'form_data': 'Configuration metafile will be added later.',
        })
    else:
        global factory_forms, waffle_api

        class ReturnClass(WizardClass):
            api = waffle_api
            form_list = factory_forms
        return ReturnClass.as_view()(request, *args, **kwargs)

def redirect_to_homepage(request):
    response = redirect('/wizard/initialize/')
    return response

def download_file(request):
    # Define Django project base directory
    filename = 'configuration.json'
    path = open('./core/output/configuration.json', 'r')
    # Set the mime type
    mime_type, _ = mimetypes.guess_type(filename)
    # Set the return value of the HttpResponse
    response = HttpResponse(path, content_type=mime_type)
    # Set the HTTP header for sending to browser
    response['Content-Disposition'] = "attachment; filename=%s" % filename
    # Return the response value
    return response
