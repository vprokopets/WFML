from django.shortcuts import render
from django.http import HttpResponseRedirect
from django.urls import reverse
from formtools.wizard.views import SessionWizardView
from django import forms
from collections import OrderedDict
from textX.textX import textX_API
import copy
import logging

model = {}
model_steps = []
card = {}
card_initial = {}
abstr_clafers = []
steps_validated = {}
ignore_fields = []
generated = []
api = textX_API()
logging.basicConfig(format='%(levelname)s: %(asctime)s %(message)s', level=logging.DEBUG, datefmt='%m/%d/%Y %I:%M:%S %p')
extra_step_flag = False
extra_fields = []
form_list = OrderedDict()
generated_steps = []

class WizardStepForm(forms.Form):
    """
    Form that is used to construct and validate each wizard step.
    Each wizard step represent top-level clafer in model.
    """

    def clean(self):
        """
        Function to validate wizard step form.

        RETURN
        cd (type = dict): cleaned data, that was printed to form fields.
        """
        cd = self.cleaned_data
        self.up = []
        logging.debug(f'Cleaned Data: {cd}')
        logging.debug(f'Label: {self.label}')

        # Write data from form fields to global namespace.
        api.write_to_keys(cd)

        # Validate all constraints, related to current top-level clafer.
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
                if element not in subparam.split('.')[0]:
                    subparam = element + '.' + subparam
                param_type = api.get_clafer_type(subparam)
                if param_type != 'predefined' and check_gcard(subparam) is True:
                    self.add_error(subparam, f'This field returned error: {param["error"]}')
                else:
                    self.add_error(None, f'Clafer`s {param["element"]} parameter {subparam} returned error: {param["error"]}')

        return cd

    def validation(self, element: str):
        """
        Subfunction to validate wizard step form.

        INPUTS
        element (type = str): clafer to define.
        """
        api.reset_exception_flag()
        res = api.validate_clafer(element)
        if res is not True:
            logging.debug(f'Result: {res}')
            up = api.get_unvalidated_params()
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
        cd = self.cleaned_data

        # Get required data from API.
        self.ad = api.get_abstract_dependencies()
        self.card = api.get_card()
        self.ctl, self.ctlf = api.get_cross_tree_list()
        uk = {}
        logging.debug(f'Cleaned data: {cd}')
        logging.debug(f'Abstract dependencies: {self.ad}')
        logging.debug(f'Cross-tree list: {self.ctlf}')

        # Perform printed cardinalities validation.
        for key, value in cd.items():
            key_split = key.split('_')
            logging.debug(f'Type: {key_split[0]}, Clafer: {key_split[1]}, Value: {value}')
            if key_split[0] == 'fcard':
                res = api.cardinality_solver(key_split[1], key_split[0], value)
                if res is not True:
                    uk.update({key: res})

        # Check abstract clafer cardinalities.
        # Note, that if abstract clafer has defined fcard, then total number of clafers (their fcards)
        # that are inherited from this abstract clafer MUST be in allowev values of abstract clafer fcard.
        for abs_clf in self.ad.keys():
            res = self.check_abstract_cardinalities(abs_clf)
            if res is not True:
                uk.update({None: res})

        # Check cross-tree cardinalities.
        # Note, that if some clafer is presented in any constraint of another clafer,
        # then this clafer cardinality MUST me equal 1.
        for clafer in self.ctl:
            res = self.check_cross_tree_cardinalities(clafer)
            if res is not True:
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
        key (type = str): abstract clafer to check.

        RETURN
        True (type = bool), if check was successfull.
        """
        fcard = 0
        cd_t = {}

        # Clean form input data from caridinalities prefix (fcard_)
        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        # Get abstract clafer cardinality.
        # From form input if there are.
        if key in cd_t.keys():
            value = cd_t[key]
        # From predefined record in model if there are.
        elif key in self.card['fcard'].keys():
            value = self.card['fcard'][key]
        else:
            # value = 1 UNCOMMENT IF NEED STRICTLY DEFINE ABSTRACT CLAFER REPEATS
            return True  # IF NOT
        debug = {}

        # Sum all clafers cardinalities from abstract dependencies list.
        for dependency in self.ad[key]:
            # From form input if there are.
            if dependency in cd_t.keys():
                add_value = cd_t[dependency]
            # From predefined record in model if there are.
            elif dependency in self.card['fcard'].keys():
                add_value = self.card['fcard'][dependency]
            # If cardinality is not defined anywhere, then cardinality = 1.
            else:
                add_value = 1
            fcard = fcard + add_value
            debug.update({dependency: add_value})
        logging.debug(f'Fcard: {fcard} value {value}')

        # Use cardinality solver to check
        res = api.cardinality_solver(key, 'fcard', fcard)
        if res is not True:
            return Exception(f'Invalid nested clafer cardinalities sum. Abstract clafer {key}: {value}, Sum: {fcard}. Detailed info: {debug}')
        else:
            return True

    def check_cross_tree_cardinalities(self, key: str):
        """
        Subfunction to validate Feature cardinalities definition form.
        Provides cross-tree clafer cardinalities check.

        INPUTS
        key (type = str): abstract clafer to check.

        RETURN
        True (type = bool), if check was successfull.
        """
        cd_t = {}

        # Clean form input data from caridinalities prefix (fcard_)
        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        # Get abstract clafer cardinality.
        # From form input if there are.
        if key in cd_t.keys():
            value = cd_t[key]
        # From predefined record in model if there are.
        elif key in self.card['fcard'].keys():
            value = self.card['fcard'][key]
        # If cardinality is not defined anywhere, then cardinality = 1.
        else:
            value = 1
        # If some clafer is presented in any constraint of another clafer,
        # then this clafer cardinality MUST me equal 1.
        if value > 1:
            return Exception(f'Clafer {key} has cardinality {value} and present in cross-tree dependencies. '
                             'Please, remove these dependencies or clafer`s cardinality.')
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
        cd = self.cleaned_data
        return cd

class ModelInputForm(forms.Form):
    """
    Initial form that is used for model input.
    """

    a = """

Buttons {
    PowerButton -> predefined
    SoundButton -> predefined 2
    CypherButton -> predefined 1
    ControlButton -> predefined 0, 2..4, 7..9

    [PowerButton = 1]
    [SoundButton = 2]
    [CypherButton = 3]
    [ControlButton = 4]
}


Display {
    Type -> string
    Size -> float
    [Type in {AMOLED, IPS, TFT}]
    [Size > 0]
    [Size < 7]
    [if Size < 3 then fcard.Buttons.CypherButton = 10 else fcard.Buttons.CypherButton = 0]
}
"""
    model_field = forms.CharField(widget=forms.Textarea, initial=a)

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
        global model_steps, card, extra_fields, card_initial, extra_step_flag, generated_steps
        if step is None:
            step = self.steps.current

        logging.info(f'CALLFORM {step}')
        logging.info(f'WIZARD: {self.form_list}')
        form = super(WizardClass, self).get_form(step, data, files)
        import copy
        # Get all required data from API.
        keys = api.read_keys()
        ad = api.get_abstract_dependencies()
        generated_steps = list(dict.fromkeys(generated_steps))
        if step not in generated_steps:
            extra_step_counter = 0
            for g_s in generated_steps:
                if int(step) >= int(g_s):
                    extra_step_counter += 1
            current_step = model_steps[int(step) - extra_step_counter]
        else:
            current_step = copy.deepcopy(card_initial)
        cycles = api.get_cycle_keys()

        # Fill form label and head.
        form.label = current_step
        form.head = 'Cardinalities' if isinstance(form, type(FCardinalityForm())) or isinstance(form, type(GCardinalityForm())) else 'Clafer'
        logging.debug(f'Current step: {step} {current_step}')
        logging.debug(f'Keys: {keys}')

        # Construct FCardinalityForm for the first step.
        if isinstance(form, type(FCardinalityForm())):
            if steps_validated[int(step)] is False:
                card_update('fcard', current_step['fcard'])
                card_initial.update(copy.deepcopy(card))
            for fcard, value in current_step['fcard'].items():
                logging.debug(f'FCARD: {fcard} value {value}')
                if type(value) is not int and fcard not in ignore_fields and fcard not in ad.keys():
                    allowed = None
                    if value == '*':
                        allowed = '0..inf'
                    elif value == '+':
                        allowed = '1..inf'
                    elif value == '?':
                        allowed = '0 or 1'
                    else:
                        allowed = value
                    form.fields[f'fcard_{fcard}'] = forms.IntegerField(label=f'Feature cardinality for clafer {fcard}. Allowed values: {allowed}')

        # Construct GCardinalityForm for the first step.
        elif isinstance(form, type(GCardinalityForm())):
            # Update cardinalities according to fcard data from the previous step.
            if step == '1':
                if steps_validated[int(step)] is False:
                    card_update('gcard', current_step['gcard'])
                    card_initial.update(copy.deepcopy(card))
                    upd_gcard()
            else:
                copyd = {'gcard': {}}
                for item in extra_fields:
                    for key in item.keys():
                        copyd['gcard'].update({key: current_step['gcard'][key.split('_')[0]]})
                current_step = copyd
            # Create fields for each gcard record.
            for gcard, value in current_step['gcard'].items():
                logging.debug(f'GCARD: {gcard} value {value}')
                logging.debug(f'IGNORE: {ignore_fields}')

                # For number type gcard create integer field.
                # TODO check this functionality.
                if type(value) is not int and value not in ['xor', 'or', 'mux', 'opt'] and gcard not in ignore_fields:
                    form.fields[f'gcard_{gcard}'] = forms.IntegerField(label=f'Feature cardinality for clafer {gcard}. Allowed values: {value}')

                # For xor or or cardinality create choices list or checkboxes respectively.
                elif value == 'xor' or value == 'or':
                    abstract_clafers = api.get_abstract_dependencies()
                    gcards = []
                    check = ''
                    flag = False
                    for part in gcard.split('.'):
                        # If gcard is defined for abstract clafer, then such cardinality will be applied
                        # to all clafers, thar are inherited from this abstract clafer.
                        # Step by step reconstruct gcard value, and check each step for presence in abstract clafers.
                        if flag is False:
                            if check == '':
                                check = part
                            else:
                                check = check + '.' + part
                            if check in abstract_clafers.keys():
                                for k in abstract_clafers[check]:
                                    if k not in generated:
                                        repeats, struct = get_fcard(k)
                                    else:
                                        repeats = 1
                                    # Multiply gcard fields if fcard > 1.
                                    for repeat in range(0, repeats):
                                        if repeats > 1:
                                            name = name_generation(k, struct, repeat, False)
                                            api.mapping(k, name)
                                            gcards.append(name)
                                        else:
                                            gcards.append(k)
                                flag = True
                        # If abstract clafer is matched with step value, then just add last steps to ALL multiplied gcard records.
                        else:
                            for gc in range(0, len(gcards)):
                                gcards[gc] = gcards[gc] + '.' + part

                    # If there are no abstract clafers, that will match any part of gcard value, then just add this gcard.
                    # TODO check this section on fcard support.
                    if gcards == [] and flag is False:
                        if gcard not in generated:
                            repeats, struct = get_fcard(gcard)
                        else:
                            repeats = 1
                        # Multiply gcard fields if fcard > 1.
                        for repeat in range(0, repeats):
                            if repeats > 1:
                                name = name_generation(gcard, struct, repeat, False)
                                api.mapping(gcard, name)
                                gcards.append(name)
                            else:
                                gcards.append(gcard)
                    logging.debug(f'GCARDS FULLFILLED: {gcards}')

                    # Create appropriate fields in form.
                    for item in gcards:
                        key = api.read_certain_key(item, True)
                        values = key[item]
                        choises_list = []
                        for v in values:
                            choises_list.append((v, v))
                        # Ignore fields are used to ensure correctness of form.
                        # SessionWizardView validates each form twice: right after their filling and in the end.

                        # If some field, that should not be in the model according to their cardinality
                        # will not be added to ignore fields, then SessionWizardView will require to fill these fields
                        # during the final validation.
                        if item not in ignore_fields:
                            ignore_fields.append(item)
                        flag = check_gcard(item)
                        if value == 'xor' and flag is True:
                            form.fields[f'gcard_{item}'] = forms.ChoiceField(choices=choises_list)
                        elif value == 'or' and flag is True:
                            form.fields[f'gcard_{item}'] = forms.MultipleChoiceField(choices=choises_list, widget=forms.CheckboxSelectMultiple)

        # Construct WizardStepForm for the all other steps.
        else:
            extra_fields = []
            # If step contains cycle, then get all cycle items and perform field initialization for all of them.
            if current_step in cycles.keys():
                for element in cycles[current_step]:
                    logging.debug(f'Element: {element}')
                    keys_step = keys[element]
                    for keypair in keys_step:
                        for key, value in keypair.items():
                            logging.debug(key, value)
                            key = element + '.' + key

                            # Generated list is used to prevent field multiplication during form revalidation.
                            # During form initialization if fcard of field > 1, then copies of this field are generated.
                            # During revalidation (in the end), this code is reexecuted one more time, so we need to prevent
                            # multiplication of generated fields.
                            if key not in generated:
                                repeats, struct = get_fcard(key)
                            else:
                                repeats = 1
                            logging.debug(f'REPEATS: {repeats}')

                            # Create fields for all records (generated and standard).
                            for repeat in range(0, repeats):
                                if repeats > 1:
                                    name = name_generation(key, struct, repeat)
                                    api.mapping(key, name)
                                    if key not in ignore_fields:
                                        ignore_fields.append(key)
                                else:
                                    name = key
                                # Check if this field is allowed by chosen group cardinality.
                                flag = check_gcard(key)
                                if value['type'] == 'integer' and name not in ignore_fields and flag is True:
                                    form.fields[name] = forms.IntegerField(label=name)
                                elif value['type'] == 'float' and name not in ignore_fields and flag is True:
                                    form.fields[name] = forms.FloatField(label=name)
                                elif value['type'] == 'string' and name not in ignore_fields and flag is True:
                                    form.fields[name] = forms.CharField(label=name)
                                elif value['type'] == 'boolean' and name not in ignore_fields and flag is True:
                                    choises_list = []
                                    for v in [True, False]:
                                        choises_list.append((v, v))
                                    form.fields[name] = forms.ChoiceField(choices=choises_list, widget=forms.RadioSelect)
            else:
                keys_step = keys[current_step]
                logging.debug(f'KEYS STEP: {keys_step}')
                for keypair in keys_step:
                    for key, value in keypair.items():
                        key = current_step + '.' + key
                        # Generated list is used to prevent field multiplication during form revalidation.
                        # During form initialization if fcard of field > 1, then copies of this field are generated.
                        # During revalidation (in the end), this code is reexecuted one more time, so we need to prevent
                        # multiplication of generated fields.
                        if key not in generated:
                            repeats, struct = get_fcard(key)
                        else:
                            repeats = 1
                        logging.debug(f'REPEATS: {repeats}')
                        logging.debug(f'Key: {key}, Value: {value}')

                        for repeat in range(0, repeats):
                            if repeats > 1:
                                name = name_generation(key, struct, repeat)
                                api.mapping(key, name)
                                if key not in ignore_fields:
                                    ignore_fields.append(key)
                            else:
                                name = key
                            # Check if this field is allowed by chosen group cardinality.
                            flag = check_gcard(name)

                            if value['type'] == 'integer' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.IntegerField(label=name)
                            elif value['type'] == 'float' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.FloatField(label=name)
                            elif value['type'] == 'string' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.CharField(label=name)
                            elif value['type'] == 'array' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.CharField(label=name)
                            elif value['type'] == 'integerArray' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.CharField(label=name)
                            elif value['type'] == 'floatArray' and name not in ignore_fields and flag is True:
                                form.fields[name] = forms.CharField(label=name)
                            elif value['type'] == 'boolean' and name not in ignore_fields and flag is True:
                                choises_list = []
                                for v in [True, False]:
                                    choises_list.append((v, v))
                                form.fields[name] = forms.ChoiceField(choices=choises_list, widget=forms.RadioSelect)
                # Sort fields by names. This will group generated fields.
                form.fields = OrderedDict(sorted(form.fields.items()))
        api.cardinalities_upd(card)
        return form

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
                card_update(key_split[0], {key_split[1]: value})
        logging.info(f'STEP {step} FINISHED. CARDINALITIES: {card}')
        return self.get_form_step_data(form)

    def render_next_step(self, form, **kwargs):
        """
        This method gets called when the next step/form should be rendered.
        `form` contains the last/current form.
        """
        global extra_step_flag, generated_steps
        if extra_step_flag is True:
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
        if extra_step_flag is True:
            extra_step_flag = False
        return self.render(new_form, **kwargs)

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
            global model, model_steps, abstr_clafers, generated_steps, card_initial, card
            model = form.cleaned_data['model_field']
            logging.info(f'Model: {model}')
            model_steps = api.initialize_product(model)
            abstr_clafers = api.get_abstract_clafers()
            global steps_validated, ignore_fields, generated, extra_step_flag, extra_fields, form_list
            steps_validated = {}
            ignore_fields = []
            generated = []
            generated_steps = []
            extra_fields = []
            form_list = OrderedDict()
            extra_step_flag = False
            card_initial = {}
            card = {}
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

def card_update(card_type: str, card_value):
    """
    Update card table according to card type.

    INPUTS
    card_type (variable type): type of cardinality (fcard, gcard)
    card_value: cardinality value
    not_initial_flag (type = bool): flag shows that function is calles not in feature cardinalities definition step.
    """
    global card
    logging.debug(card)
    for key in ['fcard', 'gcard']:
        if key not in card.keys():
            card.update({key: {}})
    if card_type == 'fcard':
        card['fcard'].update(card_value)
    else:
        card['gcard'].update(card_value)
    logging.debug(f'Card is updated: {card}')

    if card_type == 'fcard':
        upd_gcard()
        for k, v in card_value.items():
            if type(v) is int:
                api.update_global_namespace('fcard_' + k, v)
                logging.debug(f'Global namespace mappings for clafer {k}, was created {v} times.')

def get_fcard(clafer: str):
    """
    Get complex feature cardinality of clafer. This includes cardinalities of all super direct
    and super indirect clafers.

    INPUTS
    clafer: clafer name

    RETURN
    ret (type = int): clafer complex feature cardinality;
    struct (type = dict): structure of complex cardinality (clafer name: cardinality)
    For example,
    a 2 {
        b 3
    }
    ret: 6
    struct: {a: 2, b: 3}
    """
    global card
    ret = 1
    struct = {}
    abstract_clafers = api.get_abstract_dependencies()
    check = ''

    # Check for abstract clafer.
    for part in clafer.split('.'):
        if check == '':
            check = part
        else:
            check = check + '.' + part
        for k, v in abstract_clafers.items():
            if check in v:
                check = k
    logging.debug(f'ABSTR: {abstr_clafers}')
    logging.debug(f'CARD: {card}')
    logging.debug(f'CHECK: {check}')
    for key in card['fcard'].keys():
        if key in clafer or key in check:
            if key not in abstr_clafers:
                struct.update({key.split('.')[-1]: card['fcard'][key]})
                ret = ret * card['fcard'][key]
    logging.debug(f'RET: {ret}, STRUCT: {struct}')
    return ret, struct

def check_gcard(clafer: str):
    """
    Check, whether clafer is allowed according to group cardinality.

    INPUTS
    clafer: clafer to check.

    RETURN
    (type = bool): check result.
    """
    global card
    logging.debug(f'GcardTable: {card["gcard"]}')
    for key, value in card['gcard'].items():
        if key == clafer:
            return True
        if type(value) is not list:
            value = [value]
        # This method checks all parts of clafer full path to be sure, that all cardinalities are valid.
        for item in value:
            check = key + '.' + item
            if check in clafer:
                return True
        if key in clafer:
            return False
    return True

def upd_gcard():
    """
    Update group cardinality if it was multiplied according to feature cardinality.
    """
    global card, extra_step_flag, extra_fields
    rm_keys = []
    add_keys = []
    fcard = 1
    for key, value in card['gcard'].items():
        repeats, struct = get_fcard(key)
        for repeat in range(0, repeats):
            if repeats > 1:
                name = name_generation(key, struct, repeat)
                if name not in card['gcard'].keys():
                    if steps_validated[1] is True:
                        logging.info('Extra Step Flag was set!')
                        extra_step_flag = True
                    api.mapping(key, name)
                    if key not in ignore_fields:
                        ignore_fields.append(key)
                    if key not in rm_keys:
                        rm_keys.append(key)
                    for index in range(0, fcard):
                        add_keys.append({name: value})
            else:
                name = key
    # If gcard was multiplied, we need to add generated keys and remove the original key from card table.
    logging.debug(f'RM KEYS {rm_keys}')
    logging.debug(f'ADD KEYS {add_keys}')
    if extra_fields == []:
        extra_fields = add_keys
    for key in rm_keys:
        card['gcard'].pop(key, None)
    for key in add_keys:
        card['gcard'].update(key)
    logging.debug(f'CARD WAS UPD {card["gcard"]}')

def get_card():
    return card

def name_generation(original_name: str, struct: dict, repeat: int, flag=True):
    """
    Generate name for clafer with cardinality > 1 according to complex cardinality structure.

    INPUTS
    original_name: original clafer name;
    struct: structure of complex cardinality (clafer name: cardinality);
    repeat: sequentional number of generated clafer.

    RETURN
    ret (type = str): generated name

    For example, 6 sequentilnal function execution with different repeat values will generate:
    a 2 {
        b 3
    }
    complex cardinality: 6
    original name: b
    struct: {a: 2, b: 3}
    repeat: 0..5
    result: a0.b0, a0.b1, a0.b2, a1.b0, a1.b1, a1.b2
    """
    from functools import reduce
    threshold = reduce((lambda x, y: x * y), struct.values())
    name = original_name.split('.')
    res = ''
    for part in name:
        if part in struct.keys():
            threshold = threshold / struct[part]
            suffix = repeat / threshold
            repeat = repeat % threshold
            name = part + '_' + str(int(suffix))
        else:
            name = part
        if res == '':
            res = name
        else:
            res = res + '.' + name
    logging.debug(f'Original {original_name} -> generated: {res}')
    if flag:
        generated.append(res)
    return res
