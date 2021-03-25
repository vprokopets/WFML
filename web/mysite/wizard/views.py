from django.core.exceptions import ValidationError
from django.shortcuts import render
from django.http import HttpResponseRedirect
from django.urls import reverse
from formtools.wizard.views import SessionWizardView
from django import forms
from collections import OrderedDict
from wizard.forms import Form1, Form2, Form3, CardinalityForm, GCardinalityForm

model = {}
model_steps = []
card = {}
abstr_clafers = []
steps_validated = {}
ignore_fields = []
generated = []

class ChoiceWizardView(SessionWizardView):
    def done(self, form_list, **kwargs):
        global model, model_steps
        model = {}
        model_steps = []
        return render(self.request, 'done.html', {
            'form_data': [form.cleaned_data for form in form_list],
        })

    def get_form(self, step=None, data=None, files=None):
        form = super(ChoiceWizardView, self).get_form(step, data, files)
        if 'choice_field' in form.fields:
            form1_cleaned_data = self.get_cleaned_data_for_step('0')
            if form1_cleaned_data:
                form.fields['choice_field'].choices = [item for item in form1_cleaned_data.items()]
        if step == '1':
            form.fields['generated'] = forms.CharField(label='generated')
        return form


class WizardClass(SessionWizardView):
    def done(self, form_list, **kwargs):
        from textX.textX import save_json
        res = save_json()
        print(f'FINALRESULT!!!: {res}')

        return render(self.request, 'done.html', {
            'form_data': res,
        })

    def get_form(self, step=None, data=None, files=None):
        global model_steps, card
        if step is None:
            step = self.steps.current
        print(f'CALLFORM {step}')
        print(f'WIZARD: {type(self).form_list}')
        form = super(WizardClass, self).get_form(step, data, files)

        from textX.textX import read_keys, write_to_keys, get_cycle_keys, mapping, cardinalities_upd, get_abstract_dependencies
        keys = read_keys()
        ad = get_abstract_dependencies()
        current_step = model_steps[int(step)]
        cycles = get_cycle_keys()
        form.label = current_step
        form.head = 'Cardinalities' if int(step) == 0 else 'Clafer'
        print(f'Current step: {int(step)} {current_step}')
        print(f'Keys: {keys}')
        if int(step) == 0:
            card.update(current_step)
            for fcard, value in current_step['fcard'].items():
                print(f'FCARD: {fcard} value {value}')
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

        elif int(step) == 1:
            card.update(current_step)
            upd_gcard()
            for gcard, value in current_step['gcard'].items():
                print(f'GCARD: {gcard} value {value}')
                print(f'IGNORE: {ignore_fields}')
                if type(value) is not int and value not in ['xor', 'or', 'mux', 'opt'] and gcard not in ignore_fields:
                    form.fields[f'gcard_{gcard}'] = forms.IntegerField(label=f'Feature cardinality for clafer {gcard}. Allowed values: {value}')
                elif value == 'xor' or value == 'or':
                    from textX.textX import read_certain_key, get_abstract_dependencies
                    abstract_clafers = get_abstract_dependencies()
                    gcards = []
                    check = ''
                    flag = False
                    for part in gcard.split('.'):
                        if flag is False:
                            if check == '':
                                check = part
                            else:
                                check = check + '.' + part
                            if check in abstract_clafers.keys():
                                for k in abstract_clafers[check]:
                                    print(f'k: {k}')
                                    if k not in generated:
                                        repeats, struct = get_fcard(k)
                                    else:
                                        repeats = 1
                                    for repeat in range(0, repeats):
                                        if repeats > 1:
                                            name = name_generation(k, struct, repeat, False)
                                            mapping(k, name)
                                            gcards.append(name)
                                        else:
                                            gcards.append(k)
                                flag = True
                        else:
                            for gc in range(0, len(gcards)):
                                gcards[gc] = gcards[gc] + '.' + part
                    if gcards == []:
                        gcards.append(gcard)
                    print(f'GCARDSFULLFILLED: {gcards}')
                    for item in gcards:
                        key = read_certain_key(item, True)
                        values = key[item]
                        choises_list = []
                        for v in values:
                            choises_list.append((v, v))
                        if item not in ignore_fields:
                            ignore_fields.append(item)
                        flag = check_gcard(item)
                        if value == 'xor' and flag is True:
                            form.fields[f'gcard_{item}'] = forms.ChoiceField(choices=choises_list)
                        elif value == 'or' and flag is True:
                            form.fields[f'gcard_{item}'] = forms.MultipleChoiceField(choices=choises_list, widget=forms.CheckboxSelectMultiple)

        else:
            if current_step in cycles.keys():
                for element in cycles[current_step]:
                    print(f'Element: {element}')
                    keys_step = keys[element]
                    for keypair in keys_step:
                        for key, value in keypair.items():
                            print(key, value)
                            key = element + '.' + key
                            if key not in generated:
                                repeats, struct = get_fcard(key)
                            else:
                                repeats = 1
                            print(f'REPEATS: {repeats}')
                            for repeat in range(0, repeats):
                                if repeats > 1:
                                    name = name_generation(key, struct, repeat)
                                    mapping(key, name)
                                    if key not in ignore_fields:
                                        ignore_fields.append(key)
                                else:
                                    name = key
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
                print(f'KEYSSTEP: {keys_step}')
                for keypair in keys_step:
                    for key, value in keypair.items():
                        key = current_step + '.' + key
                        if key not in generated:
                            repeats, struct = get_fcard(key)
                        else:
                            repeats = 1
                        print(f'REPEATS: {repeats}')
                        print(f'Key: {key}, Value: {value}')
                        for repeat in range(0, repeats):
                            if repeats > 1:
                                name = name_generation(key, struct, repeat)
                                mapping(key, name)
                                if key not in ignore_fields:
                                    ignore_fields.append(key)
                            else:
                                name = key
                            flag = check_gcard(name)
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
                form.fields = OrderedDict(sorted(form.fields.items()))
        cardinalities_upd(card)
        return form

    def process_step(self, form):
        step = self.steps.current
        global steps_validated
        steps_validated.update({int(step): True})
        if int(step) == 0 or int(step) == 1:
            cd = form.cleaned_data
            print(f'STEP {step} CARDINALITIES: {cd}')
            for key, value in cd.items():
                key_split = key.split('_', 1)
                card_update(key_split[0], {key_split[1]: value})
        return self.get_form_step_data(form)


def initial_page(request, *args, **kwargs):
    if request.method == 'POST':
        # Create a form instance and populate it with data from the request (binding):
        form = Form3(request.POST)
        if form.is_valid():
            from textX.textX import main_stub, get_abstract_clafers
            global model, model_steps, abstr_clafers
            model = form.cleaned_data['model_field']
            print(f'model: {model}')
            print(f'CALL MAIN THREAD {model}')
            model_steps = main_stub(model)
            abstr_clafers = get_abstract_clafers()
            global steps_validated, ignore_fields, generated
            steps_validated = {}
            ignore_fields = []
            generated = []
            for step in range(len(model_steps) - 2):
                steps_validated.update({step + 1: False})
            return HttpResponseRedirect(reverse('factory_wizard'))
    elif request.method == 'GET':
        form = Form3()
        return render(request, 'initial.html', {
            'form': form,
        })

def factory_wizard(request, *args, **kwargs):

    step_number = len(model_steps)
    ret_form_list = []
    ret_form_list.append(CardinalityForm)
    ret_form_list.append(GCardinalityForm)
    for step in range(step_number - 2):
        ret_form_list.append(Form1)

    class ReturnClass(WizardClass):
        form_list = ret_form_list
    return ReturnClass.as_view()(request, *args, **kwargs)

def card_update(card_type, card_value):
    global card
    print(card)
    print(card['fcard'])
    if card_type == 'fcard':
        card['fcard'].update(card_value)
    else:
        card['gcard'].update(card_value)
    print(f'Card is updated: {card}')

def get_fcard(clafer):
    global card
    ret = 1
    struct = {}
    from textX.textX import get_abstract_dependencies
    abstract_clafers = get_abstract_dependencies()
    check = ''
    for part in clafer.split('.'):
        if check == '':
            check = part
        else:
            check = check + '.' + part
        for k, v in abstract_clafers.items():
            if check in v:
                check = k
    print(f'ABSTR: {abstr_clafers}')
    print(f'CARD: {card}')
    print(f'CHECK: {check}')
    for key in card['fcard'].keys():
        if key in clafer or key in check:
            if key not in abstr_clafers:
                struct.update({key.split('.')[-1]: card['fcard'][key]})
                ret = ret * card['fcard'][key]
    print(f'RET: {ret}, STRUCT: {struct}')
    return ret, struct

def check_gcard(clafer):
    global card
    print(f'GcardTable: {card["gcard"]}')
    for key, value in card['gcard'].items():
        if key == clafer:
            return True
        if type(value) is not list:
            value = [value]
        for item in value:
            check = key + '.' + item
            if check in clafer:
                return True
        if key in clafer:
            return False
    return True

def upd_gcard():
    global card
    rm_keys = []
    add_keys = []
    fcard = 1
    for key, value in card['gcard'].items():
        repeats, struct = get_fcard(key)
        for repeat in range(0, repeats):
            if repeats > 1:
                name = name_generation(key, struct, repeat)
                from textX.textX import mapping
                mapping(key, name)
                if key not in ignore_fields:
                    ignore_fields.append(key)
                if key not in rm_keys:
                    rm_keys.append(key)
                for index in range(0, fcard):
                    add_keys.append({name: value})
            else:
                name = key
    print(f'RMKEYS {rm_keys}')
    print(f'ADDKEYS {add_keys}')
    for key in rm_keys:
        card['gcard'].pop(key, None)
    for key in add_keys:
        card['gcard'].update(key)
    print(f'CARD WAS UPD {card["gcard"]}')

def get_card():
    return card

def name_generation(original_name, struct, repeat, flag=True):
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
    print(f'Original {original_name} -> generated: {res}')
    if flag:
        generated.append(res)
    return res
