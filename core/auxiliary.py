def read_metadata(metamodel, name, field=None):
    for level in name.split('.'):
        metamodel = metamodel[level]
    return metamodel if field is None else metamodel['__self__'][field]