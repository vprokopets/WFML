def modulize_by_depth(tokens, depth):
    tokens_new = []
    for index in range(0, len(tokens)):
        if tokens[index]['indent'] == depth:
            tokens_new.append(tokens[index])
    return tokens_new

def modulize_by_id(tokens, token):
    tokens_new = []
    target_indent = token['indent']
    index = tokens.index(token)
    line = tokens[index]['line']
    tokens_new.append(tokens[index])
    index += 1
    while True:
        if tokens[index]['line'] == line or tokens[index]['indent'] > target_indent:
            tokens_new.append(tokens[index])
            index += 1
        else:
            break
    return tokens_new

def find_module(tokens, name):
    decompose = name.split(".")
    modulz = []
    modules = modulize_by_depth(tokens, 1)
    for module in modules:
        if module['token'] == decompose[1] and module['tag'] == 'ID':
            modulz = modulize_by_id(tokens, module)
            break
    if len(decompose) > 2:
        for index in range(2, len(decompose)):
            for module in modulz:
                if decompose[index] == module['token']:
                    modulz = modulize_by_id(tokens, module)
                    break
    return modulz

def find_parent_relations(tokens):
    for index in range(0, len(tokens)):
        if tokens[index]['token'] == "Parent":
            res = modulize_by_id(tokens, tokens[index])
            print(f"module: {res}")

            if res[1]['token'] == ':':
                print("_____________________________________")
                print(f'Parent module for child: {res}')
                print("_____________________________________")
                print(find_module(tokens, res[2]['token']))
