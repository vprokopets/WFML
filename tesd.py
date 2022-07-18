import itertools
import re
import pandas as pd
import pprint

class Gob(object):
    pass


class Truths(object):
    def __init__(self, base: list, expression: str):
        self.base = base
        self.expression = expression
        self.res = {'Base': self.base}
        # generate the sets of booleans for the bases
        self.base_conditions = list(itertools.product([False, True],
                                                      repeat=len(base)))

        # regex to match whole words defined in self.bases
        # used to add object context to variables in self.phrases
        self.p = re.compile(r'(?<!\w)(' + '|'.join(self.base) + r')(?!\w)')
        combination_index = 0
        for conditions_set in self.base_conditions:
            combination_index += 1
            self.combination = {combination_index: {}}
            for index, var in enumerate(self.base):
                self.combination[combination_index].update({var: conditions_set[index]})
            subres = self.calculate(*conditions_set)
            self.combination[combination_index].update({'Result': subres})
            self.res.update(self.combination)

    def calculate(self, *args):
        # store bases in an object context
        g = Gob()
        for a, b in zip(self.base, args):
            setattr(g, a, b)

        item = self.p.sub(r'g.\1', self.expression)
        print(item)
        return pd.eval(item)




a = Truths(['a', 'b', 'c'], '(a or c) xor b')
print(a)
pprint.pprint(a.res)

