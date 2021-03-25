

import pandas as pd
import re
card = '3..5,7,9..11'
res = []
if card == '*':
    res.append('x>=0')
elif card == '+' or card == 'or':
    res.append('x>=1')
elif card == '?' or card == 'mux':
    res.append(['x>=0', 'x<=1'])
elif card == 'xor':
    res.append('x==1')
elif type(card) == int or re.match(r'^\d+$', card):
    res.append(f'x=={card}')
else:
    strspl = card.split(',')
    for lexem in strspl:
        if re.match(r'(\d+\.\.)+\d+', lexem):
            lexspl = lexem.split('..')
            subres = []
            subres.append(f'x>={lexspl[0]}')
            subres.append(f'x<={lexspl[1]}')
            res.append(subres)
        else:
            res.append(f'x=={lexem}')
print(res)
x = 6
match_group_res = []
for match_group in res:
    if type(match_group) == list:
        subres = []
        for match in match_group:
            subres.append(pd.eval(match))
        match_group_res.append(all(subres))
    else:
        match_group_res.append(pd.eval(match_group))
print(match_group_res)
result = any(match_group_res)
if result:
    print(f'Result: {x} lies in interval {card}')
else:
    print(f'Result: {x} not lies in interval {card}')
