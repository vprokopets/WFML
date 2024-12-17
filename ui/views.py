import copy
import logging
import mimetypes
import json
import io
import pstats

from collections import OrderedDict
from core.waffle import Waffle
from django import forms
from django.http import HttpResponseRedirect
from django.http.response import HttpResponse
from django.shortcuts import redirect, render
from django.urls import reverse
from formtools.wizard.views import CookieWizardView

# profiling library
import cProfile

debug_mode = False
debug_logger = True


profiling = False
factory_forms = None
validated_steps = []
prev_steps = ['0']
successfully_validated_steps = []
model_stages = []
init_factory_forms = {}
valid = False
tlf = None

if debug_logger is True:
    logging.basicConfig(format='%(asctime)s - %(levelname)s - %(pathname)s:%(lineno)d - %(funcName)s(): %(message)s', level=logging.DEBUG, datefmt='%m/%d/%Y %I:%M:%S %p')
else:
    logging.basicConfig(format='%(asctime)s - %(levelname)s - %(message)s', level=logging.INFO, datefmt='%m/%d/%Y %I:%M:%S %p')
api = Waffle(debug_mode)


class WizardStepForm(forms.Form):
    """
    Form that is used to construct and validate each wizard step.
    """

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
        self.validate()
        """Return True if the form has no errors, or False otherwise."""
        return self.is_bound and not self.errors

    def parse_form_manually(self):
        self.manually_cleaned_data = {}
        input_data = {}
        for k, v in self.data.items():
            if (k.startswith((prefix := f'{self.prefix}-'))):
                logging.debug(f'Parsing input form {k} with value {v}')
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
                attr_type = api.read_metadata(k, 'Attribute')
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
        global valid, validated_steps, successfully_validated_steps
        logging.info(f'Validating form with validation state "{valid}": {self.__dict__}. ')
        if profiling is True:
            ob = cProfile.Profile()
            ob.enable()

        self.parse_form_manually()
        api.current_stage = tlf
        cd = copy.deepcopy(self.manually_cleaned_data)
        self.up = {}
        logging.debug(f'Label: {self.label}')
        logging.debug(f'Cleaned Data: {cd}')
        # Write data from form fields to global namespace.
        for key, value in cd.items():
            split = key.split('.', 1)
            if split[0] in ['Fcard', 'Gcard']:
                name = split[1]
                field = split[0]
                res, err = api.check_card_value(name, value, field)
                if res is False:
                    self.up.update({key: err})
            else:
                name = key
                field = 'Value'
            if self.up == {}:
                err = api.update_metadata(name, field, value)
                if err is not None:
                    self.up.update({key: err})
        if self.up == {}:
            self.validation_pipeline()
        else:
            for k, v in self.up.items():
                self.add_error(k, f'This field returned error: {v}')
            api.restore_stage_snap()
        valid = True
        if profiling is True:
            ob.disable()
            sec = io.StringIO()
            sortby = pstats.SortKey.CUMULATIVE
            ps = pstats.Stats(ob, stream=sec).sort_stats(sortby)
            ps.print_stats()

            logging.debug(sec.getvalue())
        return cd

    def validation_pipeline(self):
        res, exception_type = api.validate_constraints(tlf)
        self.error_md = api.constr_err_md
        self.constr_md = api.constr_md
        if res is not True:
            fields = self.fields.keys()
            msg, elems = res.args
            if not any([elem in fields or f'Fcard.{elem}' in fields or f'Gcard.{elem}' in fields for elem in elems]):
                self.add_error(None, f'{exception_type}: {msg}')
            else:
                for elem in elems:
                    attr_type = api.read_metadata(elem, 'Attribute')
                    for field in self.fields.keys():
                        if attr_type != 'predefined' and (elem == field or f'Fcard.{elem}' == field or f'Gcard.{elem}' == field):
                            self.add_error(field, f'{exception_type}: {msg}')
            api.restore_stage_snap()
        else:
            if self.prefix not in successfully_validated_steps:
                successfully_validated_steps.append(self.prefix)

        # # Assign unvalidated parameters error to appropriate fields.
        # for param in self.up:
        #     element = param['element']
        #     field_flag = False
        #     for subparam in param['params']:
        #         original = api.get_original_name(subparam)
        #         param_type = api.namespace[original.split('.')[0]]['Features'][original]['Type']
        #         for field in self.fields.keys():
        #             if param_type != 'predefined' and (subparam == field or f'Fcard.{subparam}' == field or f'Gcard.{subparam}' == field):
        #                 self.add_error(field, f'This field returned error: {param["error"]}')
        #                 field_flag = True
        #     if param['params'] == () or param['params'] == [] or field_flag is False:
        #         self.add_error(None, f'Feature`s {param["element"]} returned error: {param["error"]}')
        # if self.up != []:
        #     api.restore_stage_snap()
        # elif self.up == [] and not (cd != {} and list(cd.keys())[0].split('.')[0] in ['Fcard', 'Gcard']):
        #     if self.label in cycles.keys():
        #         for element in cycles[self.label]:
        #             api.namespace[element]['Validated'] = True
        #     else:
        #         api.namespace[self.label]['Validated'] = True


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
        res = api.save_json()
        logging.info(f'! Final result: {res}')

        return render(self.request, 'done.html', {
            'form_data': res,
            'history': json.dumps(api.configuration_history, indent=4),
            'history_selected': {},
            'collapsable': list(api.configuration_history.keys()),
            'metadata': json.dumps(api.metamodel, indent=4),
            'metadata_selected': {},
            'selected_feature': None
        })

    def get_form(self, step=None, data=None, files=None):
        """
        ! This method is automatically called after the previous step of wizard was successfully validated.

        Method to construct form for current wizard step.

        RETURN
        form with all required fields.
        """

        # Create form object.
        global model_stages, step_current, tlf, init_factory_forms, prev_steps, successfully_validated_steps
        if step is None:
            step = self.steps.current
        step_current = step

        self.form = super(WizardClass, self).get_form(step, data, files)

        self.current_step = model_stages[int(step)]
        logging.info(f'Wizard step {step} | {self.current_step}.')
        tlf = self.current_step

        self.form.stages_number = len(init_factory_forms)
        init_factory_forms[self.current_step] = int(step_current) + 1
        prev = list(init_factory_forms.keys()).index(self.current_step) - 1
        if prev < 0:
            gap = 0
        else:
            gap = int(init_factory_forms[list(init_factory_forms.keys())[prev]])
        self.form.stage = list(init_factory_forms.keys()).index(self.current_step) + 1
        self.form.stage_step = int(step_current) - gap + 1

        # Fill form label and head.
        self.form.label = self.current_step
        self.form.head = ''
        self.form.step_id = id(self)

        self.construct_step_form(self.current_step, files)

        if (step_current in successfully_validated_steps or step_current in prev_steps) and len(prev_steps) > 1:
            del prev_steps[-1]
        self.form.prev_step = prev_steps[-1]

        return self.form

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
        if self.current_step in cycles.keys():
            for element in (cycle_elems := cycles[self.current_step]):
                tlf_involved.append(api.get_original(element.split('-')[0].split('.')[0]))
                features_involved.append(element)
            logging.debug(f'Making cycle form group {self.current_step} || {cycle_elems}')
        elif 'Inner_Waffle_Group' in self.current_step:
            for element in (group_elems := api.groups[self.current_step]):
                tlf_involved.append(api.get_original(element.split('-')[0].split('.')[0]))
                features_involved.append(element)
            logging.debug(f'Making form group {self.current_step} || {group_elems}')
        else:
            tlf_involved.append(api.get_original(step_id.split('-')[0].split('.')[0]))
            features_involved.append(step_id)
            logging.debug(f'Making single form {self.current_step}')

        if step_current not in api.stage_snap.keys():
            form_data = {'Fcard': [], 'Gcard': [], 'Value': []}
            for tlf in tlf_involved:
                unconfigured_features = api.get_undefined_features(tlf)
                for ftype, features in unconfigured_features.items():
                    for feature in features:
                        if feature not in form_data[ftype]:
                            form_data[ftype].append(feature)
            api.save_stage_snap(step_current, form_data)
            logging.debug(f'Initializing form for {step_current}')
        else:
            form_data = api.stage_snap[step_current]['Fields']
            if files is None:
                logging.debug(f'Updating form for {step_current}')
                api.restore_stage_snap(step_current)
                logging.debug('Namespace was restored')
                self.form.full_clean()
                logging.debug(f'Cleaning form {step_current}')
                form_data = {'Fcard': [], 'Gcard': [], 'Value': []}
                for tlf in tlf_involved:
                    unconfigured_features = api.get_undefined_features(tlf)
                    for ftype, features in unconfigured_features.items():
                        for feature in features:
                            if feature not in form_data[ftype]:
                                form_data[ftype].append(feature)
                api.save_stage_snap(step_current, form_data)
        if form_data is None:
            return

        logging.debug(f'DATA {form_data} | tlf {tlf_involved} | step {step_current}')
        logging.debug(f'Features involved: {features_involved}')
        data_filtered = {
            'Fcard': [],
            'Gcard': [],
            'Value': []
        }
        for feature_type, features in form_data.items():
            for feature_name in features:
                if f'{feature_name}-{feature_type}' in features_involved:
                    data_filtered[feature_type].append(feature_name)
        logging.debug(f'Filtered features: {data_filtered}')

        self.construct_feature_cardinality_forms(data_filtered['Fcard'])
        self.construct_group_cardinality_forms(data_filtered['Gcard'])
        self.construct_attribute_value_forms(data_filtered['Value'])

        if 'Inner_Waffle_Group' in self.current_step:
            self.form.head = 'Combined step for constraint feature group'
        elif len(data_filtered['Value']) > 0:
            self.form.head = 'Values configuration for subtree of feature'
        elif len(data_filtered['Fcard']) > 0 or len(data_filtered['Gcard']) > 0:
            self.form.head = 'Cardinalities configuration for subtree of feature'
        else:
            self.form.head = 'Empty step'

        logging.info(f"Finish preparing form {self.current_step}")

    def construct_feature_cardinality_forms(self, feature_cardinalities):
        """
        Function to define a feature cardinality fields a wizard form.

        INPUTS
        feature_cardinalities (type = dict): dict with all feature cardinalities.
        """
        for fcard in feature_cardinalities:
            value = api.read_metadata(fcard, 'Fcard')
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
            value = api.read_metadata(gcard, 'Gcard')
            options_full = api.get_feature_childrens(gcard)
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
            feature_type = api.read_metadata(feature, 'Attribute')
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

    def render_next_step(self, form, **kwargs):
        """
        This method gets called when the next step/form should be rendered.
        `form` contains the last/current form.
        """
        # get the form instance based on the data from the storage backend
        # (if available).
        res = False
        skip = True
        global validated_steps, valid, prev_steps
        valid = True
        if '0' not in validated_steps:
            validated_steps.append('0')
        if self.steps.current not in prev_steps:
            prev_steps.append(self.steps.current)
        while res is False:
            logging.info(f'Rendering next step {self.steps.next}.')
            next_step = self.steps.next
            new_form = self.get_form(
                next_step,
                data=self.storage.get_step_data(next_step),
                files=self.storage.get_step_files(next_step),
            )
            if new_form.fields != {} or skip is False or next_step == self.steps.last or 'Inner_Waffle_Group_' in model_stages[int(next_step)]:
                res = True
            else:
                if next_step not in validated_steps:
                    validated_steps.append(next_step)
            # change the stored current step
            self.storage.current_step = next_step
        if next_step in validated_steps:
            valid = False
        if next_step not in validated_steps:
            validated_steps.append(next_step)
        logging.info(f'STEP {next_step} | {validated_steps} | {id(self)}')
        return self.render(new_form, **kwargs)

    def render_done(self, form, **kwargs):
        """
        This method gets called when all forms passed. The method should also
        re-validate all steps to prevent manipulation. If any form fails to
        validate, `render_revalidation_failure` should get called.
        If everything is fine call `done`.
        """
        final_forms = OrderedDict()
        # walk through the form list and try to validate the data again.
        # logging.info('RENDERIND PREV STEP')
        # for form_key in self.get_form_list():
        #     try:
        #         form_obj = self.get_form(
        #             step=form_key,
        #             data=self.storage.get_step_data(form_key),
        #             files=self.storage.get_step_files(form_key)
        #         )
        #     except KeyError:
        #         pass
        #     # if not form_obj.is_valid():
        #     #     return self.render_revalidation_failure(form_key, form_obj, **kwargs)
        #     final_forms[form_key] = form_obj

        # render the done view and reset the wizard before returning the
        # response. This is needed to prevent from rendering done with the
        # same data twice.
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
            model = form.cleaned_data['model_field']
            if 'Manual' in request.POST.keys():
                global model_stages, validated_steps, step_current, factory_forms, tlf, init_factory_forms, successfully_validated_steps, valid
                valid = True
                step_current, tlf = None, None
                validated_steps, model_stages, factory_forms = [], [], []
                successfully_validated_steps = []
                init_factory_forms = {}

                logging.info(f'Model: {model}')
                model_stages_unfiltered = api.initialize_product(model)
                for stage in model_stages_unfiltered:
                    if not stage.startswith('Constraint_'):
                        factory_forms.append(WizardStepForm)
                        init_factory_forms.update({stage: 0})
                        model_stages.append(stage)
                return HttpResponseRedirect(reverse('factory_wizard'))
            else:
                api.generate_product(model)
                res = api.save_json()
                return render(request, 'done.html', {
                    'form_data': res,
                })

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
        res = api.save_json()
        logging.info(f'! Product configuration was not finished. You can always continue from this place: {res}')

        return render(request, 'done.html', {
            'form_data': res,
        })
    else:
        class ReturnClass(WizardClass):
            form_list = factory_forms
        return ReturnClass.as_view()(request, *args, **kwargs)

def redirect_to_homepage(request):
    response = redirect('/wizard/initialize/')
    return response

def download_file(request):
    # Define Django project base directory
    filename = 'configuration.json'
    path = api.get_json()
    # Set the mime type
    mime_type, _ = mimetypes.guess_type(filename)
    # Set the return value of the HttpResponse
    response = HttpResponse(path, content_type=mime_type)
    # Set the HTTP header for sending to browser
    response['Content-Disposition'] = "attachment; filename=%s" % filename
    # Return the response value
    return response

def configure_metadata_output(request):
    if request.method == 'POST':
        selected_feature = request.POST.get('feature-list')
        print(f'POST: {selected_feature}')
        history_selected = json.dumps(api.configuration_history[selected_feature], indent=4)
        metadata_selected = json.dumps(api.read_metadata(selected_feature.split('-')[0]), indent=4)
    else:
        history_selected, metadata_selected = {}, {}
        selected_feature = None
    return render(request, 'done.html', {
        'form_data': api.save_json(),
        'history': json.dumps(api.configuration_history, indent=4),
        'history_selected': history_selected,
        'collapsable': list(api.configuration_history.keys()).sort(),
        'metadata': json.dumps(api.metamodel, indent=4),
        'metadata_selected': metadata_selected,
        'selected_feature': selected_feature.split('-')[0]
    })
