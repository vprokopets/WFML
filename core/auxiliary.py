from core.graph import Graph

def read_feature_data(metamodel, name, field=None):
    for level in name.split('.'):
        metamodel = metamodel[level]
    return metamodel if field is None else metamodel['__self__'][field]

def cname(obj):
    """
    Function to return class name of object.

    INPUTS
    obj: object to check.

    RETURN
    (type = string): object`s class name.
    """
    return obj.__class__.__name__

def topo_sort(deps, rev=False):
    graph = Graph()
    for dep in deps:
        graph.add_edge(dep)

    seq, cycles = graph.topo_sort()
    if rev is True:
        seq.reverse()
    return seq, cycles

def is_card_defined(value):
    return False if (value in ['*', '+', '?', 'xor', 'or']
                    or (isinstance(value, str) and (len(value.split(',')) > 1 or len(value.split('..')) > 1))) else True
