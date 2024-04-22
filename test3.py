import copy

deps = [('A.B-Fcard', 'A.B-Gcard'),
 ('A-Gcard', 'A.B-Fcard'),
 ('A.C-Fcard', 'A.C-Gcard'),
 ('A-Gcard', 'A.C-Fcard'),
 ('A-Fcard', 'A-Gcard'),
 ('D.E-Fcard', 'D.E-Gcard'),
 ('D-Gcard', 'D.E-Fcard'),
 ('D-Fcard', 'D-Gcard'),
 ('D.E-Fcard', '[fcard.D.E == 0]'),
 ('A.C-Fcard', '[fcard.D.E == 1]'),
 ('A.C-Fcard', 'D.E-Fcard'),
 ('A.B-Fcard', '[fcard.D.E == 0]'),
 ('D.E-Fcard', '[fcard.D.E == 1]'),
 ('A.B-Fcard', 'D.E-Fcard')]


flat_dict = {}

elem_pattern = {
   'Before': [],
   'After': []
}
for dep in deps:
    for index, elem in enumerate(dep):
        if elem not in flat_dict.keys():
            flat_dict.update({elem: copy.deepcopy(elem_pattern)})
        connection = 'Before' if index == 0 else 'After'
        flat_dict[elem][connection].append(dep[0 if connection == 'After' else 1])

import pprint
pprint.pprint(flat_dict)

for k, v in flat_dict.items():
    if k.startswith('[') and k.endswith(']'):
        group = v['After']
        group_filtered = []
        for elem in group:
            include = True
            for elem_alt in group:
                if (a:=elem.split('-')[0]) in (b:=elem_alt.split('-')[0]) and a != b:
                    include = False
            if include is True:
                group_filtered.append(elem)
        print(group_filtered)



