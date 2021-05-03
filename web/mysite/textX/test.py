import pickle
import pprint
objects = []
with (open("configuration.pkl", "rb")) as openfile:
    while True:
        try:
            objects.append(pickle.load(openfile))
        except EOFError:
            break
for objecta in objects:
    pprint.pprint(objecta)
