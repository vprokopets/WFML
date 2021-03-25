from django import forms

class Form1(forms.Form):

    def clean(self):
        from textX.textX import write_to_keys, get_cycle_keys
        cd = self.cleaned_data
        self.up = []
        print(f'CD: {cd}')
        print(f'LABEL: {self.label}')
        write_to_keys(cd)
        cycles = get_cycle_keys()
        if self.label in cycles.keys():
            for element in cycles[self.label]:
                self.validation(element)
        else:
            self.validation(self.label)
        for param in self.up:
            element = param['element']
            for subparam in param['params']:
                if element not in subparam.split('.')[0]:
                    subparam = element + '.' + subparam
                self.add_error(subparam, param['error'])
        return cd

    def validation(self, element):
        from textX.textX import validate_clafer, reset_exception_flag, get_unvalidated_params
        reset_exception_flag()
        res = validate_clafer(element)
        if res is not True:
            print(f'RES: {res}')
            up = get_unvalidated_params()
            self.up.append({'element': element, 'params': list(dict.fromkeys(up)), 'error': res})
            print(f"UP: {up}")


class CardinalityForm(forms.Form):

    def clean(self):
        from textX.textX import cardinality_solver, get_abstract_dependencies, get_card, get_cross_tree_list
        cd = self.cleaned_data
        self.ad = get_abstract_dependencies()
        self.card = get_card()
        self.ctl, self.ctlf = get_cross_tree_list()
        uk = {}
        print(f'CD: {cd}')
        print(f'AD: {self.ad}')
        print(f'CRL: {self.ctlf}')
        for key, value in cd.items():
            key_split = key.split('_')
            print(f'Type: {key_split[0]}, Clafer: {key_split[1]}, Value: {value}')
            if key_split[0] == 'fcard':
                res = cardinality_solver(key_split[1], key_split[0], value)
                if res is not True:
                    uk.update({key: res})
        for abs_clf in self.ad.keys():
            res = self.check_abstract_cardinalities(abs_clf)
            if res is not True:
                uk.update({None: res})
        for clafer in self.ctl:
            res = self.check_cross_tree_cardinalities(clafer)
            if res is not True:
                uk.update({None: res})
        for key, error in uk.items():
            self.add_error(key, error)
        from textX.textX import update_global_namespace
        for key, value in cd.items():
            update_global_namespace(key, value)
        return cd

    def check_abstract_cardinalities(self, key):
        fcard = 0
        cd_t = {}

        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        if key in cd_t.keys():
            value = cd_t[key]
        elif key in self.card['fcard'].keys():
            value = self.card['fcard'][key]
        else:
            # value = 1 UNCOMMENT IF NEED STRICTLY DEFINE ABSTRACT CLAFER REPEATS
            return True  # IF NOT
        debug = {}
        for dependency in self.ad[key]:
            if dependency in cd_t.keys():
                add_value = cd_t[dependency]
            elif dependency in self.card['fcard'].keys():
                add_value = self.card['fcard'][dependency]
            else:
                add_value = 1
            fcard = fcard + add_value
            debug.update({dependency: add_value})
        print(f'CD Fcard: {fcard} value {value}')
        print(self.card)
        print(cd_t)
        from textX.textX import cardinality_solver
        res = cardinality_solver(key, 'fcard', fcard)
        if res is not True:
            return Exception(f'Invalid nested clafer cardinalities sum. Abstract clafer {key}: {value}, Sum: {fcard}. Detailed info: {debug}')
        else:
            return True

    def check_cross_tree_cardinalities(self, key):
        cd_t = {}
        for k, v in self.cleaned_data.items():
            key_split = k.split('_')
            cd_t.update({key_split[1]: v})

        if key in cd_t.keys():
            value = cd_t[key]
        elif key in self.card['fcard'].keys():
            value = self.card['fcard'][key]
        else:
            value = 1
        if value > 1:
            return Exception(f'Clafer {key} has cardinality {value} and present in cross-tree dependencies. Please, remove these dependencies or clafer`s cardinality.')
        else:
            return True

class GCardinalityForm(forms.Form):

    def clean(self):
        cd = self.cleaned_data
        return cd

class Form2(forms.Form):
    choice_field = forms.ChoiceField()

class Form3(forms.Form):
    a = """

General {
    NumberOfWorkers -> integer
    result_storage -> string
    [NumberOfWorkers >= 1]
}

SelectionAlgorithm {
    type -> string
    [type in {Sobol, MersenneTwister}]
}

abstract OutliersDetection 5{
    MinActiveNumberOfTasks -> integer
    MaxActiveNumberOfTasks -> integer
    [MinActiveNumberOfTasks >= 3]
    [MaxActiveNumberOfTasks >= 3]
    [MinActiveNumberOfTasks <= MaxActiveNumberOfTasks]
}

or OD{
    Dixon : OutliersDetection
    Grubbs : OutliersDetection
    Chauvenet : OutliersDetection
    Quartiles : OutliersDetection
    Mad : OutliersDetection
}

abstract AbstrRepeater {
    MinTasksPerConfiguration -> integer
    MaxTasksPerConfiguration -> integer
}

xor Repeater{
    DefaultRepeater : AbstrRepeater {
        [MinTasksPerConfiguration >= 2]
        [MaxTasksPerConfiguration >= 2]
    }
    AcceptableErrorBasedRepeater: AbstrRepeater {
        [MinTasksPerConfiguration >= 1]
        [MaxTasksPerConfiguration >= 1]
        MaxFailedTasksPerConfiguration -> integer
        BaseAcceptableErrors -> integer
        ConfidenceLevels -> integer
        DevicesScaleAccuracies -> integer
        DevicesAccuracyClasses -> integer
        ExperimentAwareness {
            isEnabled -> boolean
            MaxAcceptableErrors -> integer
            RatiosMax -> integer
        }
    }
}

abstract TreeParzenEstimator {
    Parameters {
        TopNPercent -> integer
        RandomFraction -> integer
        BandwidthFactor -> integer
        MinBandwirth -> float
        SamplingSize -> integer
    }
}

abstract MultiArmedBandit {
    Parameters {
        xor cType{
            int
            float
            std
        }
        c -> float
        [if gcard.cType == float then 0 <= c]
        [if gcard.cType == float then c <= 1]
        [if gcard.cType == std then c = std]
    }
}

abstract ModelMock

abstract SciKitLearn {
    Type -> string
    Parameters {
        SamplingSize -> integer
        MinimalScore -> float
        CrossValidationSplits -> integer
        TestSize -> float
        DataPreprocessing {
            OrdinalHyperparameter -> string
            NominalHyperparameter -> string
            IntegerHyperparameter -> string
            FloatHyperparameter -> string
        }
        UnderlyingModelParameters {
            n_iter -> integer
            tol -> float
            normalize -> boolean
        }
    }
}

Predictor {
    WindowSize -> float
    xor Models 1..5 {
        TPE : TreeParzenEstimator
        MAB : MultiArmedBandit
        MM : ModelMock
        skLearn : SciKitLearn
    }
}

StopConditionTriggerLogic {
    Expression -> string
    InspectionParameters {
        RepetitionPerion -> integer
        TimeUnit -> string
        [RepetitionPerion > 0]
    }
}

abstract StopCondition {
    Name -> string
    Type -> predefined
}

QuantityBasedSC : StopCondition 1..5{
    Parameters {
        MaxConfigs -> integer
        [MaxConfigs > 0]
    }
    [Type = QuantityBased]
}

GuaranteedSC : StopCondition 1 {
    [Type = Guaranted]
}

BadConfigurationBasedSC : StopCondition 1..5{
    Parameters {
        MaxBadConfigurations -> integer
        [MaxBadConfigurations > 0]
    }
    [Type = BadConfigurationBased]
}

ImprovementBasedSC : StopCondition 1..5{
    Parameters {
        MaxConfigsWithoutImprovement -> integer
        [MaxConfigsWithoutImprovement > 0]
    }
    [Type = ImprovementBased]
}

TimeBasedSC : StopCondition 1..5{
    Parameters {
        MaxRunTime -> integer
        TimeUnit -> string
        [MaxRunTime > 0]
    }
    [Type = TimeBased]
}

"""
    model_field = forms.CharField(widget=forms.Textarea, initial=a)
