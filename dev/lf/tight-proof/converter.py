#!/usr/bin/env python

# run as ./converter in.v out.v to generate a new file out.v with old notations replaced

import sys

with open(sys.argv[1], 'r') as infile:
    contents = infile.read()

# returns the next term in text
def getTerm(text):
    # things that indicate the term is finished
    stop = [' ', ')', '.']

    parens = 0

    spaces = True
    parenStart = False

    for i, c in enumerate(text):
        if spaces:
            if c == ' ':
                continue
            else:
                if c == '(':
                    parenStart = True
                    parens += 1
                spaces = False
                continue

        if parens == 0 and ((parenStart == False and c in stop) or (parenStart == True)):
            # print(text[0:i])
            return text[0:i]
        elif c == '(':
            parens += 1
        elif c == ')':
            parens -= 1

    raise Exception(text)

def stripExtraParens(term):
    while len(term) >= 2 and term[0] == '(' and term[-1] == ')':
        term = term[1:-1]
    return term

notations = [('ty_trm', '|-', '::'), 
             ('subtyp', '|-', '<:'), 
             ('ty_def', '/-', '::'), 
             ('ty_defs', '/-', ':::'),
             ('ty_trm_p', '|-!', '::'),
             ('ty_trm_t', '|-#', '::'),
             ('subtyp_t', '|-#', '<:'),
             ('tight_pt', '|-##', '::'),
             ('tight_pt_v', '|-##v', '::')]

for old, a, b in notations:
    last = 0
    while True:
        last = contents.find(' ' + old + ' ', last)
        if last == -1: break

        # delete the old notation
        contents = contents[:last] + contents[last:].replace(' ' + old + ' ', ' ', 1)
        last += 1

        # context
        term = getTerm(contents[last:])
        stripped = stripExtraParens(term)
        contents = contents[:last] + contents[last:].replace(term, stripped, 1) + ' '
        last += len(stripped) + 1

        # a
        term = getTerm(contents[last:])
        stripped = stripExtraParens(term)
        contents = contents[:last] + a + ' ' + contents[last:].replace(term, stripped, 1) + ' '
        last += len(stripped) + len(a) + 2

        # b
        term = getTerm(contents[last:])
        stripped = stripExtraParens(term)
        contents = contents[:last] + b + ' ' + contents[last:].replace(term, stripped, 1)
        last += len(stripped) + len(b) + 1

outfile = open(sys.argv[2], 'w')
outfile.write(contents)
