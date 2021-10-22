import pprint

a = {'param1': 1}
b = {'param1': 2, 'param2': 2}
c = {'param1': 2, 'param2': 2}
d = {'param1': 3}
e = {'param1': 4, 'param2': 4}
f = {'param1': 5, 'param2': 5}


input = {'top': {'kv1': a, 'kv2': b, 'kv3': {'kv31': c, 'kv32': d, 'kv33': {'kv331': e, 'kv332': f}}}}

pprint.pprint(input)

def find_unique(input, key, res=None):
    if res is None:
        res = []
    for k, v in input.items():
        print(f'Debug. Key: {key}, k: {k}, v: {v}, res: {res}')
        if k == key and v not in res:
            print(f'Debug. Key {key} was added.')
            res.append(v)
        if type(v) is dict:
            find_unique(v, key, res)
    return res


result = find_unique(input, 'param1')
result2 = find_unique(input, 'param2')
print(result)
print(result2)
