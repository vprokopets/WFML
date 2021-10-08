import copy
import logging

from core.wfml import textX_API
from django.shortcuts import render
from django.http import HttpResponseRedirect
from django.urls import reverse
from formtools.wizard.views import SessionWizardView
from django import forms
from collections import OrderedDict


model = {}
model_steps = []
card = {}
card_initial = {}
abstr_features = []
steps_validated = {}
ignore_fields = []
generated = []
api = textX_API()
logging.basicConfig(format='%(levelname)s: %(asctime)s %(message)s', level=logging.DEBUG, datefmt='%m/%d/%Y %I:%M:%S %p')
extra_step_flag = False
extra_fields = []
form_list = OrderedDict()
generated_steps = []
step = ''
done = False

class WizardStepForm(forms.Form):
    """
    Form that is used to construct and validate each wizard step.
    Each wizard step represent top-level feature in model.
    """

    def clean(self):
        """
        Function to validate wizard step form.

        RETURN
        cd (type = dict): cleaned data, that was printed to form fields.
        """
        global step_current, done
        if done is False:
            api.get_stage_snap(step_current)
        cd = self.cleaned_data
        self.up = []
        logging.debug(f'Cleaned Data: {cd}')
        logging.debug(f'Label: {self.label}')

        # Write data from form fields to global namespace.
        api.write_to_keys(cd)

        # Validate all constraints, related to current top-level feature.
        cycles = api.get_cycle_keys()
        if self.label in cycles.keys():
            for element in cycles[self.label]:
                self.validation(element)
        else:
            self.validation(self.label)

        # Assign unvalidated parameters error to appropriate fields.
        for param in self.up:
            element = param['element']
            for subparam in param['params']:
                param_type = api.get_feature_type(subparam)
                if param_type != 'predefined' and subparam in self.fields:
                    self.add_error(subparam, f'This field returned error: {param["error"]}')
                else:
                    self.add_error(None, f'feature`s {param["element"]} parameter {subparam} returned error: {param["error"]}')

        return cd

    def validation(self, element: str):
        """
        Subfunction to validate wizard step form.

        INPUTS
        element (type = str): feature to define.
        """
        api.reset_exception_flag()
        res = api.validate_feature(element)
        if res is not True:
            logging.debug(f'Result: {res}')
            up = api.get_wfml_data('Iterable.UnvalidatedFeatures')
            self.up.append({'element': element, 'params': list(dict.fromkeys(up)), 'error': res})
            logging.debug(f"Unvalidated parameter: {up}")


class FCardinalityForm(forms.Form):
    """
    Form that is used to construct and validate feature cardinalities definition step.
    Feature cardinalities definition is always the first step in wizard.
    """

    def clean(self):
        """
        Function to validate Feature cardinalities definition form.

        RETURN
        cd (type = dict): cleaned data, that was printed to form fields.
        """
        global step_current, done
        if done is False:
            api.get_stage_snap(step_current)
        cd = self.cleaned_data

        # Get required data from API.
        self.ad = api.get_wfml_data('Dependencies.Abstract')
        self.card = api.get_wfml_data('Cardinalities')
        self.ctl = api.get_wfml_data('Features.CrossTree')
        uk = {}
        logging.debug(f'Cleaned data: {cd}')
        logging.debug(f'Abstract dependencies: {self.ad}')
        logging.debug(f'Cross-tree list: {self.ctl.keys()}')

        # Perform printed cardinalities validation.
        for key, value in cd.items():
            key_split = key.split('_')
            logging.debug(f'Type: {key_split[0]}, feature: {key_split[1]}, Value: {value}')
            if key_split[0] == 'fcard':
                res = api.cardinality_solver(key_split[1], key_split[0], value)
                if res is not True:
                    uk.update({key: res})

        # Check abstract feature cardinalities.
        # Note, that if abstract feature has defined fcard, then total number of features (their fcards)
        # that are inherited from this abstract feature MUST be in allowev values of abstract feature fcard.
        for abs_clf in self.ad.keys():
            res = self.check_abstract_cardinalities(abs_clf)
            if res is not True:
                pass
                # uk.update({None: res})

        # Check cross-tree cardinalities.
        # Note, that if some feature is presented in any constraint of another feature,
        # then this feature cardinality MUST me equal 1.
        disabled = True
        for feature in self.ctl.keys():
            res = self.check_cross_tree_cardinalities(feature)
            if res is not True and disabled is False:
                uk.update({None: res})

        # Assign errors to form fields, if exist.
        for key, error in uk.items():
            self.add_error(key, error)

        return cd

    def check_abstract_cardinalities(self, key: str):
        """
        Subfunction to validate Feature cardinalities definition form.
        Provides abstract cardinalities check.

        INPUTS
        key (type = str): abstract feature to check.

        RETURN
        True (type = bool), if check was successfull.
        """
        fcard = 0
        cd_t = {}

        # Clean form input data from caridinalities prefix (fcard_)
        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        # Get abstract feature cardinality.
        # From form input if there are.
        if key in cd_t.keys():
            value = cd_t[key]
        # From predefined record in model if there are.
        elif key in self.card['Feature'].keys():
            value = self.card['Feature'][key]
        else:
            # value = 1 UNCOMMENT IF NEED STRICTLY DEFINE ABSTRACT feature REPEATS
            return True  # IF NOT
        debug = {}

        # Sum all features cardinalities from abstract dependencies list.
        for dependency in self.ad[key]:
            # From form input if there are.
            if dependency in cd_t.keys():
                add_value = cd_t[dependency]
            # From predefined record in model if there are.
            elif dependency in self.card['Feature'].keys():
                add_value = self.card['Feature'][dependency]
            # If cardinality is not defined anywhere, then cardinality = 1.
            else:
                add_value = 1
            fcard = fcard + add_value
            debug.update({dependency: add_value})
        logging.debug(f'Fcard: {fcard} value {value}')

        # Use cardinality solver to check
        res = api.cardinality_solver(key, 'fcard', fcard)
        if res is not True:
            return Exception(f'Invalid nested feature cardinalities sum. Abstract feature {key}: {value}, Sum: {fcard}. Detailed info: {debug}')
        else:
            return True

    def check_cross_tree_cardinalities(self, key: str):
        """
        Subfunction to validate Feature cardinalities definition form.
        Provides cross-tree feature cardinalities check.

        INPUTS
        key (type = str): abstract feature to check.

        RETURN
        True (type = bool), if check was successfull.
        """
        cd_t = {}

        # Clean form input data from caridinalities prefix (fcard_)
        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        # Get abstract feature cardinality.
        # From form input if there are.
        if key in cd_t.keys():
            value = cd_t[key]
        # From predefined record in model if there are.
        elif key in self.card['Feature'].keys():
            value = self.card['Feature'][key]
        # If cardinality is not defined anywhere, then cardinality = 1.
        else:
            value = 1
        # If some feature is presented in any constraint of another feature,
        # then this feature cardinality MUST me equal 1.
        if value > 1:
            return Exception(f'feature {key} has cardinality {value} and present in cross-tree dependencies. '
                             'Please, remove these dependencies or feature`s cardinality.')
        else:
            return True

class GCardinalityForm(forms.Form):
    """
    ! GCardinalityForm consists only of selection fields (radio button or checkboxes),
    so no additional validation is need.

    Form that is used to construct and validate group cardinalities definition step.
    Group cardinalities definition is always the second step in wizard.
    """

    def clean(self):
        global step_current, done
        if done is False:
            api.get_stage_snap(step_current)
        uk = {}
        cd = self.cleaned_data
        gcards = api.get_wfml_data('CardinalitiesInitial.Group')
        for card in cd.keys():
            subcard_type = card.split('_', 1)[0]
            subcard = card.split('_', 1)[1]
            if gcards[subcard] not in ('or', 'xor') and api.cardinality_solver(subcard, subcard_type, len(cd[card])) is not True:
                msg = f'Wrong number of {card} Group Cardinality items (Total {len(cd[card])} items: {cd[card]}). Correct value is: {gcards[subcard]}'
                uk.update({card: msg})
        for key, error in uk.items():
            self.add_error(key, error)
        return cd

class ModelInputForm(forms.Form):
    """
    Initial form that is used for model input.
    """

    initial_text = ''
    model_field = forms.CharField(widget=forms.Textarea, initial=initial_text)

class WizardClass(SessionWizardView):

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
        })

    def get_form(self, step=None, data=None, files=None):
        """
        ! This method is automatically called after the previous step of wizard was successfully validated.

        Method to construct form for current wizard step.

        RETURN
        form with all required fields.
        """

        # Create form object.
        global model_steps, card, extra_fields, card_initial, extra_step_flag, generated_steps, step_current, done
        if step is None:
            step = self.steps.current
        step_current = step
        if done is False:
            api.get_stage_snap(step)
        logging.info(f'Wizard step {step}.')
        self.form = super(WizardClass, self).get_form(step, data, files)

        self.ad = api.get_wfml_data('Dependencies.Abstract')
        generated_steps = list(dict.fromkeys(generated_steps))
        if step not in generated_steps:
            extra_step_counter = 0
            for g_s in generated_steps:
                if int(step) >= int(g_s):
                    extra_step_counter += 1
            current_step = model_steps[int(step) - extra_step_counter]
        else:
            current_step = copy.deepcopy(card_initial)

        # Fill form label and head.
        self.form.label = current_step
        self.form.head = 'Cardinalities' if isinstance(self.form, type(FCardinalityForm())) \
            or isinstance(self.form, type(GCardinalityForm())) else 'Feature'
        logging.debug(f'Current step: {step} {current_step}')

        # Construct FCardinalityForm for Feature Cardinality definition steps.
        if isinstance(self.form, type(FCardinalityForm())):
            self.construct_feature_cardinality_form()

        # Construct GCardinalityForm for Group Cardinality definition steps.
        elif isinstance(self.form, type(GCardinalityForm())):
            self.construct_group_cardinality_form()

        # Construct WizardStepForm for the all other steps.
        else:
            cycles = api.get_cycle_keys()
            extra_fields = []
            # If step contains cycle, then get all cycle items and perform field initialization for all of them.
            if current_step in cycles.keys():
                for element in cycles[current_step]:
                    self.construct_step_form(element)
            else:
                self.construct_step_form(current_step)
        return self.form

    def construct_feature_cardinality_form(self):
        feature_cardinalities = api.get_wfml_data('Cardinalities.Feature')
        for fcard, value in feature_cardinalities.items():
            logging.debug(f'FCARD: {fcard} value {value}')
            if type(value) is not int and fcard not in ignore_fields and fcard not in self.ad.keys():
                allowed = None
                if value == '*':
                    allowed = '0..inf'
                elif value == '+':
                    allowed = '1..inf'
                elif value == '?':
                    allowed = '0 or 1'
                else:
                    allowed = value
                self.form.fields[f'fcard_{fcard}'] = forms.IntegerField(label=f'Feature Cardinality for Feature {fcard}. Allowed values: {allowed}')

    def construct_group_cardinality_form(self):
        # Create fields for each gcard record.
        group_cardinalities = api.get_wfml_data('Cardinalities.Group')
        for gcard, value in group_cardinalities.items():
            logging.debug(f'GCARD: {gcard} value {value}')
            logging.debug(f'IGNORE: {ignore_fields}')

            # Create appropriate fields in form.
            key = api.read_certain_key(gcard, True)
            values = key[gcard]
            choises_list = []
            for v in values:
                choises_list.append((v, v))
            # Ignore fields are used to ensure correctness of form.
            # SessionWizardView validates each form twice: right after their filling and in the end.

            # If some field, that should not be in the model according to their cardinality
            # will not be added to ignore fields, then SessionWizardView will require to fill these fields
            # during the final validation.
            if gcard not in ignore_fields:
                ignore_fields.append(gcard)
            if value == 'xor':
                self.form.fields[f'gcard_{gcard}'] = forms.ChoiceField(choices=choises_list)
            else:
                self.form.fields[f'gcard_{gcard}'] = forms.MultipleChoiceField(choices=choises_list,
                                                                                widget=forms.CheckboxSelectMultiple)

    def construct_step_form(self, step):
        keys_step = api.read_certain_key(step, False)
        logging.debug(f'KEYS STEP: {keys_step}')
        for key, values in keys_step.items():
            for subkey, value in values.items():
                field_name = f'{key}.{subkey}'
                # Generated list is used to prevent field multiplication during form revalidation.
                # During form initialization if fcard of field > 1, then copies of this field are generated.
                # During revalidation (in the end), this code is reexecuted one more time, so we need to prevent
                # multiplication of generated fields.

                logging.debug(f'Key: {key}, Value: {value}')
                # Check if this field is allowed by chosen group cardinality.

                if value['type'] == 'integer':
                    self.form.fields[field_name] = forms.IntegerField(label=field_name)
                elif value['type'] == 'float':
                    self.form.fields[field_name] = forms.FloatField(label=field_name)
                elif value['type'] == 'string' or \
                        value['type'] == 'array' or \
                        value['type'] == 'integerArray' or \
                        value['type'] == 'floatArray':
                    self.form.fields[field_name] = forms.CharField(label=field_name)
                elif value['type'] == 'boolean':
                    choises_list = []
                    for v in [True, False]:
                        choises_list.append((v, v))
                    self.form.fields[field_name] = forms.ChoiceField(choices=choises_list, widget=forms.RadioSelect)
        # Sort fields by names. This will group generated fields.
        self.form.fields = OrderedDict(sorted(self.form.fields.items()))

    def process_step(self, form):
        """
        ! This method is automatically called after the first and the second steps of wizard was successfully validated.

        Method to update cardinality table for the next steps.

        RETURN
        form with all required fields.
        """
        step = self.steps.current
        global steps_validated
        steps_validated.update({int(step): True})
        if isinstance(form, type(FCardinalityForm())) or isinstance(form, type(GCardinalityForm())):
            cd = form.cleaned_data
            logging.info(f'STEP {step} CARDINALITIES: {cd}')
            for key, value in cd.items():
                key_split = key.split('_', 1)
                if key_split[0] == 'fcard':
                    api.update_wfml_data('Cardinalities.Feature', {key_split[1]: value})
                else:
                    api.update_wfml_data('Cardinalities.Group', {key_split[1]: value})

        if isinstance(form, type(FCardinalityForm())):
            api.validate_common_constraints()
            api.mapping()
        elif isinstance(form, type(GCardinalityForm())):
            api.apply_group_cardinalities()
        api.update_wfml_data('Iterable.Stage', step)
        api.snap_step_data(step)
        logging.info(f'STEP {step} FINISHED. CARDINALITIES: {card}')
        #logging.debug(pprint.pprint(api.show_wfml_data()))
        return self.get_form_step_data(form)

    def render_next_step(self, form, **kwargs):
        """
        This method gets called when the next step/form should be rendered.
        `form` contains the last/current form.
        """
        global generated_steps
        if api.get_wfml_data('Flags.ExtraStep') is True and self.steps.current != '0':
            for index in range(len(self.form_list) - 1, int(self.steps.current), -1):
                self.form_list[str(index + 1)] = self.form_list[str(index)]
            self.form_list[str(int(self.steps.current) + 1)] = GCardinalityForm
            logging.info('Rendering additional step.')
            global form_list
            form_list = self.form_list
            generated_steps.append(str(int(self.steps.current) + 1))
        # get the form instance based on the data from the storage backend
        # (if available).
        logging.info('Rendering next step.')
        next_step = self.steps.next
        new_form = self.get_form(
            next_step,
            data=self.storage.get_step_data(next_step),
            files=self.storage.get_step_files(next_step),
        )
        # change the stored current step
        self.storage.current_step = next_step
        api.update_wfml_data('Flags.ExtraStep', False)
        return self.render(new_form, **kwargs)

    def render_done(self, form, **kwargs):
        """
        This method gets called when all forms passed. The method should also
        re-validate all steps to prevent manipulation. If any form fails to
        validate, `render_revalidation_failure` should get called.
        If everything is fine call `done`.
        """
        global done
        done = True
        final_forms = OrderedDict()
        # walk through the form list and try to validate the data again.
        for form_key in self.get_form_list():
            try:
                form_obj = self.get_form(
                    step=form_key,
                    data=self.storage.get_step_data(form_key),
                    files=self.storage.get_step_files(form_key)
                )
            except KeyError:
                pass
            # if not form_obj.is_valid():
            #     return self.render_revalidation_failure(form_key, form_obj, **kwargs)
            final_forms[form_key] = form_obj

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
            global model, model_steps, abstr_features, generated_steps, card_initial, card, step_current
            model = form.cleaned_data['model_field']
            logging.info(f'Model: {model}')
            model_steps = api.initialize_product(model)
            abstr_features = api.get_wfml_data('Features.Abstract').keys()
            global steps_validated, ignore_fields, generated, extra_fields, form_list, done
            steps_validated = {}
            ignore_fields = []
            generated = []
            generated_steps = []
            extra_fields = []
            form_list = OrderedDict()
            card_initial = {}
            card = {}
            step_current = ''
            done = False
            for step in range(len(model_steps)):
                steps_validated.update({step: False})
            return HttpResponseRedirect(reverse('factory_wizard'))

    elif request.method == 'GET':
        form = ModelInputForm()
        return render(request, 'initial.html', {
            'form': form,
        })

def factory_wizard(request, *args, **kwargs):
    """
    ! 2 Additional steps are added for FCardinalityForm and GCardinalityForm.

    This method constructs wizard according with the number of steps, defined in model.

    RETURN
    wizard
    """
    if request.method == 'POST' and 'mybtn2' in request.POST.keys():
        print(f'DSADAD {request.POST.keys()}')
        res = api.save_json()
        logging.info(f'! Product configuration was not finished. You could always continue from this place: {res}')

        return render(request, 'done.html', {
            'form_data': res,
        })
    else:
        step_number = len(model_steps)
        ret_form_list = []
        if form_list == OrderedDict():
            ret_form_list.append(FCardinalityForm)
            ret_form_list.append(GCardinalityForm)
            for step in range(step_number - 2):
                ret_form_list.append(WizardStepForm)
        else:
            for index in form_list:
                form = form_list[index]
                if form == type(FCardinalityForm()):
                    ret_form_list.append(FCardinalityForm)
                elif form == type(GCardinalityForm()):
                    ret_form_list.append(GCardinalityForm)
                else:
                    ret_form_list.append(WizardStepForm)

        class ReturnClass(WizardClass):
            form_list = ret_form_list
        return ReturnClass.as_view()(request, *args, **kwargs)
