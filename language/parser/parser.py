import math


class Parser():

    def __init__(self):
        pass

    def preprocessing(self, tokens):
        tokens = self.find_all_parent_child_relations(tokens)
        tokens = self.find_dependencies(tokens)
        tokens = self.cardinality_decompose(tokens)
        return tokens

    def filter_by_depth(self, tokens, depth):
        tokens_new = []
        for index in range(0, len(tokens)):
            if tokens[index]['indent'] == depth:
                tokens_new.append(tokens[index])
        return tokens_new

    def modulize_by_id(self, tokens, token):
        tokens_new = []
        target_indent = token['indent']
        index = tokens.index(token)
        line = tokens[index]['line']
        tokens_new.append(tokens[index])
        index += 1
        while True:
            try:
                if tokens[index]['line'] == line or tokens[index]['indent'] > target_indent and token['tag'] == 'ID':
                    tokens_new.append(tokens[index])
                    index += 1
                else:
                    break
            except IndexError:
                break
        return tokens_new

    def find_module(self, tokens, name):
        decompose = name.split(".")
        modulz = []
        modules = self.filter_by_depth(tokens, 1)
        for module in modules:
            if module['token'] == decompose[1] and module['tag'] == 'ID':
                modulz = self.modulize_by_id(tokens, module)
                break
        if len(decompose) > 2:
            for index in range(2, len(decompose)):
                for module in modulz:
                    if decompose[index] == module['token']:
                        modulz = self.modulize_by_id(tokens, module)
                        break
        return modulz

    def find_token_by_id(self, tokens, token_id):
        for token in tokens:
            if token['id'] == token_id:
                return token
        return 'No tokens with such ID registered'

    def find_all_parent_child_relations(self, tokens, indent=0):
        child = True
        while child:
            parent = True if indent > 0 else False
            child = True if self.filter_by_depth(tokens, indent + 1) != [] else False
            for token in self.filter_by_depth(tokens, indent):
                if parent:
                    upper_indent_tokens = self.filter_by_depth(tokens, indent - 1)
                    for token_u in upper_indent_tokens:
                        if token in self.modulize_by_id(tokens, token_u) and token['tag'] == 'ID':
                            token['parent'] = token_u['id']
                if child:
                    lower_indent_tokens = self.filter_by_depth(tokens, indent + 1)
                    childs = []
                    for token_l in lower_indent_tokens:
                        if token_l in self.modulize_by_id(tokens, token) and token_l['tag'] == 'ID':
                            childs.append(token_l['id'])
                    if childs:
                        token['childs'] = childs
            indent += 1
        return tokens

    def find_dependencies(self, tokens):
        for token in tokens:
            dependencies = []
            try:
                for child_token in token['childs']:
                    if self.find_token_by_id(tokens, child_token)['token'] == 'Dependency':
                        dependency = {}
                        dependency_module = self.modulize_by_id(tokens, self.find_token_by_id(tokens, child_token))
                        if dependency_module[1]['token'] == ':':
                            dependency['target_id'] = self.find_module(tokens, dependency_module[2]['token'])[0]['id']
                            if dependency_module[0]['childs']:
                                dependency['condition'] = dependency_module[0]['childs'][len(dependency_module[0]['childs']) - 1]
                        dependencies.append(dependency)
                if dependencies != []:
                    token['dependencies'] = dependencies
            except KeyError:
                pass
        return tokens

    def cardinality_decompose(self, tokens):
        for token in tokens:
            if token['tag'] == "CARDINALITY":
                decompose = token['token'].split(' ')
                while True:
                    try:
                        decompose.remove('')
                    except ValueError:
                        break
                token['token'] = decompose
        return tokens
