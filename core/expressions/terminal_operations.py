import itertools
import logging

from core.expressions.expression_base import ExpressionElement


class term(ExpressionElement):
    @property
    def value(self):
        """
        Function to check type of op value (variable, number, string, etc.) and return it.

        RETURN
        op (variable type): variable, number, string, etc.
        """
        op = self.op
        if isinstance(op, ExpressionElement):
            logging.debug(f"Operation object: {op} with value {type(op)}")
            res = self._get_value(op._parse(self.mapping_md, self.constr_md))
            return self._get_value(op._parse(self.mapping_md, self.constr_md))
        elif isinstance(op, str) and op not in self.api.workspace.keywords:
            is_list = True if any(op.startswith(x[0]) and op.endswith(x[1]) for x in [('[', ']'), ('{', '}')]) else False

            replace_patterns = ['[', ']', '{', '}', "'", '"', ' ']
            for pattern in replace_patterns:
                op = op.replace_patternsace(pattern, '')
            res = [self._autoconvert(x) for x in op.split(',')] if is_list is True else self._autoconvert(op)
            if self.mapping_md['FilterFlag'] is not None:
                op = self._get_value({'Fname': res, 'Ftype': 'Value', 'IsFeature': False})
                if res != op:
                    logging.debug(f'Filter term successfully swapped from {res} to {op}')
                    res = op

        else:
            res = op

        logging.debug(f'Term object {res}')
        return res

    def _parse(self, mapping_md, constr_md):
        self.mapping_md = mapping_md
        self.constr_md = constr_md
        if (obj_id := id(self)) in constr_md['Features'].keys():
            obj_md = constr_md['Features'][obj_id]
            fname = mapping_md['Current'][(orig := list(obj_md.keys())[0])]
            ftype = list(obj_md.values())[0]
            ret = self.api.workspace.read_metadata(fname)['__self__']
            childs = self.api.workspace.get_feature_childrens(fname)
            ret.update({'GFcard': len(set(itertools.chain.from_iterable([sub[orig]] for sub in mapping_md['All']))),
                        'Fname': fname,
                        'Ftype': ftype,
                        'IsFeature': True,
                        'Childs': childs})
            if mapping_md['ExceptionFlag'] is False:
                self.exception, mapping_md['ExceptionFlag'] = True, True
                self._check_exception(self._boolify(ret), f'Expression {fname}')
        else:
            ret = {'IsFeature': False,
                   'Value': self.value}

        return ret

    def _boolify_str(self, string):
        if string == 'True':
            return True
        if string == 'False':
            return False
        raise ValueError('String value is not Boolean.')

    def _autoconvert(self, string):
        for fn in (self._boolify_str, int, float):
            try:
                return fn(string)
            except ValueError:
                pass
        return string
