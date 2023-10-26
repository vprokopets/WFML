import copy
import logging
import pprint
import mimetypes
from core.waffle import Waffle
from django.shortcuts import redirect, render
from django.http import HttpResponseRedirect
from django.http.response import HttpResponse
from django.urls import reverse
from formtools.wizard.views import CookieWizardView
from django import forms
from collections import OrderedDict

# profiling library
import cProfile
import pstats
import io
from pstats import SortKey
from OpenModelicaPlugin.pn_models import PetriNetModels
import OpenModelicaPlugin.OMPNLibGenerator as OMPNLibGenerator

profiling = False
factory_forms = None
generated_steps = []
model_stages = []
init_factory_forms = {}
tlf = None
api = Waffle()

logging.basicConfig(format="%(levelname)s: %(asctime)s %(message)s", level=logging.INFO, datefmt="%m/%d/%Y %I:%M:%S %p")


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
        if profiling is True:
            ob = cProfile.Profile()
            ob.enable()

        cd = copy.copy(self.cleaned_data)

        logging.debug(f"Cleaned Data: {cd}")
        logging.debug(f"Label: {self.label}")
        # Write data from form fields to global namespace.
        if cd != {} and list(cd.keys())[0].split(".")[0] in ["Fcard", "Gcard"]:
            self.up = {}
            check = []
            cards_step = True
            for key, value in cd.items():
                res = api.cardinality_solver(key, value)
                check.append(res)
                if res is not True:
                    self.up.update({key: res})
            for key, error in self.up.items():
                self.add_error(key, error)
            if all(x is True for x in check):
                api.update_namespace(cd)
        else:
            api.update_namespace(cd)
            cards_step = False
        # Validate all constraints, related to current top-level feature.
        self.up = []
        cycles = api.cycles
        if self.label in cycles.keys():
            for element in cycles[self.label]:
                self.validation(element, cards_step)
        else:
            self.validation(self.label, cards_step)
        # Assign unvalidated parameters error to appropriate fields.
        for param in self.up:
            element = param["element"]
            field_flag = False
            for subparam in param["params"]:
                original = api.get_original_name(subparam)
                param_type = api.namespace[original.split(".")[0]]["Features"][original]["Type"]
                for field in self.fields.keys():
                    if param_type != "predefined" and (
                        subparam == field or f"Fcard.{subparam}" == field or f"Gcard.{subparam}" == field
                    ):
                        self.add_error(field, f'This field returned error: {param["error"]}')
                        field_flag = True
            if param["params"] == () or param["params"] == [] or field_flag is False:
                self.add_error(None, f'Feature`s {param["element"]} returned error: {param["error"]}')
        if self.up != []:
            api.restore_stage_snap()
        elif self.up == [] and not (cd != {} and list(cd.keys())[0].split(".")[0] in ["Fcard", "Gcard"]):
            if self.label in cycles.keys():
                for element in cycles[self.label]:
                    api.namespace[element]["Validated"] = True
            else:
                api.namespace[self.label]["Validated"] = True
        if profiling is True:
            ob.disable()
            sec = io.StringIO()
            sortby = SortKey.CUMULATIVE
            ps = pstats.Stats(ob, stream=sec).sort_stats(sortby)
            ps.print_stats()

            logging.debug(sec.getvalue())
        return cd

    def validation(self, element: str, cards: bool):
        """
        Subfunction to validate wizard step form.

        INPUTS
        element (type = str): feature to define.
        """
        res = api.validate_feature(element, cards)
        if res is not True:
            logging.debug(f"Result: {res}")
            up = api.iterable["UnvalidatedFeatures"]
            self.up.append({"element": element, "params": up, "error": res})
            logging.debug(f"Unvalidated parameter: {up}")


class ModelInputForm(forms.Form):
    """
    Initial form that is used for model input.
    """

    initial_text = ""
    model_field = forms.CharField(widget=forms.Textarea(attrs={"id": "textarea"}), initial=initial_text)


class WizardClass(CookieWizardView):
    def done(self, form_list, **kwargs):
        """
        ! This method is automatically called after the last step of wizard was successfully validated.

        RETURN
        redirection to final page.
        """
        res = api.save_json()
        logging.info(f"! Final result: {res}")

        # check json for DPN or HPN, return pn_models_done.html if true
        if "DPN" in res or "HPN" in res:
            return render(
                self.request,
                "pn_models_done.html",
                {
                    "form_data": res,
                },
            )

        return render(
            self.request,
            "done.html",
            {
                "form_data": res,
            },
        )

    def get_form(self, step=None, data=None, files=None):
        """
        ! This method is automatically called after the previous step of wizard was successfully validated.

        Method to construct form for current wizard step.

        RETURN
        form with all required fields.
        """

        # Create form object.
        global model_stages, generated_steps, step_current, tlf, init_factory_forms
        if step is None:
            step = self.steps.current
        step_current = step
        logging.info(f"Wizard step {step}.")
        self.form = super(WizardClass, self).get_form(step, data, files)

        generated_steps = list(dict.fromkeys(generated_steps))
        if step not in generated_steps:
            extra_step_counter = 0
            for g_s in generated_steps:
                if int(step) >= int(g_s):
                    extra_step_counter += 1
            self.current_step = model_stages[int(step) - extra_step_counter]
            tlf = self.current_step
        else:
            self.current_step = tlf

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
        self.form.head = ""
        logging.info(f"Current step: {step} {self.current_step}")

        cycles = api.cycles
        # If step contains cycle, then get all cycle items and perform field initialization for all of them.
        if self.current_step in cycles.keys():
            for element in cycles[self.current_step]:
                self.construct_step_form(element)
        else:
            self.construct_step_form(self.current_step)
        return self.form

    def construct_step_form(self, tlf):
        """
        Function to define a fields a wizard form.

        INPUTS
        tlf (type = string): name of top-level feature.
        """
        snap_name = f"{tlf}_{step_current}" if step_current in generated_steps else tlf
        if snap_name not in api.stage_snap.keys():
            data = api.preprocess_step(tlf)
            api.save_stage_snap(snap_name, data)
            if data == "Empty stage":
                return
        else:
            data = api.stage_snap[snap_name]["Fields"]
        if data is None or data == "Empty stage":
            return
        if "Fcard" in data.keys() and "Gcard" in data.keys():
            self.construct_feature_cardinality_form(data["Fcard"])
            self.construct_group_cardinality_form(data["Gcard"])
            self.form.head = "Cardinalities"
        else:
            self.form.head = "Features"
            for feature in data["Value"]:
                # Generated list is used to prevent field multiplication during form revalidation.
                # During form initialization if fcard of field > 1, then copies of this field are generated.
                # During revalidation (in the end), this code is reexecuted one more time, so we need to prevent
                # multiplication of generated fields.
                feature_type = api.get_feature_input_type(feature)
                # Check if this field is allowed by chosen group cardinality.
                if feature_type == "integer":
                    self.form.fields[feature] = forms.IntegerField(label=feature)
                elif feature_type == "float":
                    self.form.fields[feature] = forms.FloatField(label=feature)
                elif (
                    feature_type == "string"
                    or feature_type == "array"
                    or feature_type == "integerArray"
                    or feature_type == "floatArray"
                ):
                    self.form.fields[feature] = forms.CharField(label=feature)
                elif feature_type == "boolean":
                    choises_list = []
                    for v in [True, False]:
                        choises_list.append((v, v))
                    self.form.fields[feature] = forms.ChoiceField(
                        label=feature, choices=choises_list, widget=forms.RadioSelect
                    )
                # Sort fields by names. This will group generated fields.
                self.form.fields = OrderedDict(sorted(self.form.fields.items()))

    def construct_feature_cardinality_form(self, feature_cardinalities):
        """
        Function to define a feature cardinality fields a wizard form.

        INPUTS
        feature_cardinalities (type = dict): dict with all feature cardinalities.
        """
        for fcard in feature_cardinalities:
            value = api.get_feature(f"Fcard.{fcard}")["Fcard"]
            allowed = None
            if value == "*":
                allowed = "0..inf"
            elif value == "+":
                allowed = "1..inf"
            elif value == "?":
                allowed = "0 or 1"
            else:
                allowed = value
            self.form.fields[f"Fcard.{fcard}"] = forms.IntegerField(
                label=f"Feature Cardinality for Feature {fcard}. Allowed values: {allowed}"
            )

    def construct_group_cardinality_form(self, group_cardinalities):
        """
        Function to define a group cardinality fields a wizard form.

        INPUTS
        group_cardinalities (type = dict): dict with all group cardinalities.
        """
        # Create fields for each gcard record.
        for gcard in group_cardinalities:
            # Create appropriate fields in form.
            value = api.get_feature(f"Gcard.{gcard}")["Gcard"]
            options = api.get_feature_childrens(gcard)
            choises_list = []
            for option in options:
                choises_list.append((option, option))
            # Ignore fields are used to ensure correctness of form.
            # CookieWizardView validates each form twice: right after their filling and in the end.

            if value == "xor":
                self.form.fields[f"Gcard.{gcard}"] = forms.ChoiceField(
                    label=f"Gcard.{gcard}", choices=choises_list, widget=forms.RadioSelect
                )
            else:
                self.form.fields[f"Gcard.{gcard}"] = forms.MultipleChoiceField(
                    label=f"Gcard.{gcard}", choices=choises_list, widget=forms.CheckboxSelectMultiple
                )
            # Fix for lowercase label
            self.form.fields[f"Gcard.{gcard}"].label = f"Gcard.{gcard}"

    def process_step(self, form):
        """
        ! This method is automatically called after the first and the second steps of wizard was successfully validated.

        Method to update cardinality table for the next steps.

        RETURN
        form with all required fields.
        """
        step = self.steps.current
        self.check = None
        # api.restore_stage_snap()
        logging.info(f"STEP {step} FINISHED.")
        cycles = api.cycles
        if self.current_step in cycles.keys():
            for element in cycles[self.current_step]:
                self.check = api.preprocess_step(element) if self.check is None else True
        else:
            self.check = api.preprocess_step(tlf)
        global factory_forms
        if self.check is not None:
            factory_forms.append(None)
            for index in range(len(self.form_list) - 1, int(self.steps.current), -1):
                self.form_list[str(index + 1)] = self.form_list[str(index)]
                factory_forms[index + 1] = factory_forms[index]
            self.form_list[str(int(self.steps.current) + 1)] = WizardStepForm
            factory_forms[int(self.steps.current) + 1] = WizardStepForm
            logging.info("Rendering additional step.")
            generated_steps.append(str(int(self.steps.current) + 1))

        return self.get_form_step_data(form)

    def render_next_step(self, form, **kwargs):
        """
        This method gets called when the next step/form should be rendered.
        `form` contains the last/current form.
        """
        # get the form instance based on the data from the storage backend
        # (if available).
        logging.info("Rendering next step.")
        next_step = self.steps.next
        new_form = self.get_form(
            next_step,
            data=self.storage.get_step_data(next_step),
            files=self.storage.get_step_files(next_step),
        )
        # change the stored current step
        self.storage.current_step = next_step
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
        for form_key in self.get_form_list():
            try:
                form_obj = self.get_form(
                    step=form_key,
                    data=self.storage.get_step_data(form_key),
                    files=self.storage.get_step_files(form_key),
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
    if request.method == "POST":
        # Create a form instance and populate it with data from the request (binding):
        form = ModelInputForm(request.POST)
        if form.is_valid():
            global model_stages, generated_steps, step_current, factory_forms, tlf, init_factory_forms
            factory_forms, step_current, tlf = None, None, None
            generated_steps, model_stages = [], []
            init_factory_forms = {}
            model = form.cleaned_data["model_field"]
            logging.info(f"Model: {model}")
            model_stages = api.initialize_product(model)
            factory_forms = [WizardStepForm for _ in range(len(model_stages))]
            for stage in model_stages:
                init_factory_forms.update({stage: 0})
            return HttpResponseRedirect(reverse("factory_wizard"))

    elif request.method == "GET":
        form = ModelInputForm()
        return render(
            request,
            "initial.html",
            {
                "form": form,
            },
        )


def factory_wizard(request, *args, **kwargs):
    """
    This method constructs wizard according with the number of steps, defined in model.

    RETURN
    wizard
    """
    if request.method == "POST" and "mybtn2" in request.POST.keys():
        res = api.save_json()
        logging.info(f"! Product configuration was not finished. You can always continue from this place: {res}")

        return render(
            request,
            "done.html",
            {
                "form_data": res,
            },
        )
    else:

        class ReturnClass(WizardClass):
            form_list = factory_forms

        return ReturnClass.as_view()(request, *args, **kwargs)


def redirect_to_homepage(request):
    response = redirect("/wizard/initialize/")
    return response


def download_file(request):
    # Define Django project base directory
    filename = "configuration.json"
    path = api.get_json()
    # Set the mime type
    mime_type, _ = mimetypes.guess_type(filename)
    # Set the return value of the HttpResponse
    response = HttpResponse(path, content_type=mime_type)
    # Set the HTTP header for sending to browser
    response["Content-Disposition"] = "attachment; filename=%s" % filename
    # Return the response value
    return response


def use_pn_models(request, *args, **kwargs):
    """
    ! This method is automatically called to render petrinet initial page (GET request)
    or to process filled ModelInputForm and create wizard with petrinet models(POST request).

    RETURN
    initial page (GET)
    redirect to wizard (POST)
    """
    if request.method == "POST":
        # add pn model to input
        inputDict = request.POST.copy()
        if request.POST["pn_type"] == "dpn":
            inputDict["model_field"] = PetriNetModels.dpn_model
        else:
            inputDict["model_field"] = PetriNetModels.hpn_model

        # Create a form instance and populate it with data from the request (binding) and selected pn model:
        form = ModelInputForm(inputDict)
        if form.is_valid():
            global model_stages, generated_steps, step_current, factory_forms, tlf, init_factory_forms
            factory_forms, step_current, tlf = None, None, None
            generated_steps, model_stages = [], []
            init_factory_forms = {}
            model = form.cleaned_data["model_field"]
            logging.info(f"Model: {model}")
            model_stages = api.initialize_product(model)
            factory_forms = [WizardStepForm for _ in range(len(model_stages))]
            for stage in model_stages:
                init_factory_forms.update({stage: 0})
            return HttpResponseRedirect(reverse("factory_wizard"))

    elif request.method == "GET":
        form = ModelInputForm()
        return render(
            request,
            "pn_models.html",
            {
                "form": form,
            },
        )


def download_modelica_file(request):
    json_path = "./core/output/configuration.json"
    PNLib_file = OMPNLibGenerator.wfml_json_to_om_pnlib_file(json_path)
    response = HttpResponse(PNLib_file, content_type="application/mo")
    response["Content-Disposition"] = "attachment; filename=%s" % "output.mo"
    return response
