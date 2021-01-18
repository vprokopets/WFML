import sys
import re
import uuid


def lex(characters, token_exprs):
    pos = 0
    indent = 0
    tokens = []
    line = 1
    while pos < len(characters):
        match = None
        for token_expr in token_exprs:
            pattern, tag = token_expr
            regex = re.compile(pattern)
            match = regex.match(characters, pos)
            if match:
                text = match.group(0)
                if tag:
                    if tag == "NEWLINE":
                        line += 1
                        indent = indentation(text)
                    elif tag != "TAB":
                        token = {"token": text, "tag": tag, "indent": indent, "id": uuid.uuid1(), "line": line}
                        tokens.append(token)
                break
        if not match:
            print(f'Illegal character: {characters[pos]} on position {pos}.')
            sys.exit(1)
        else:
            pos = match.end(0)
    return tokens

def indentation(s, tabsize=4):
    sx = s.expandtabs(tabsize)
    return (len(sx) - len(sx.lstrip()) - s.count('\n')) / tabsize
