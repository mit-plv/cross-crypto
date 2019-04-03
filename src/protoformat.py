#!/usr/bin/python3


import argparse
import re
import string


def main():
    p = argparse.ArgumentParser()
    p.add_argument('file')
    args = p.parse_args()
    with open(args.file) as f:
        program = []
        bindings = {}
        for (i, l) in enumerate(f):
            l = l.strip().split(maxsplit=2)

            if l[0] == 'input':
                bindings[l[2]] = i
                program.append('(op_input {})'.format(l[1]))
                continue
            if l[0] == 'output':
                program.append('(op_output {} {})'.format(
                        l[1],
                        format_ref(bindings, i, parse_tuples(l[2])[0])))
                continue

            if l[1] == '=':
                bindings[l[0]] = i
                program.append('(op_const {})'.format(l[2]))
                continue

            if l[1] == '<-':
                bindings[l[0]] = i
                if l[2] == '$':
                    program.append('op_rand')
                    continue
                rhs = parse_tuples(l[2])
                if len(rhs) == 2:
                    program.append('(op_app {} {})'.format(
                            rhs[0],
                            format_ref(bindings, i, rhs[1])))
                    continue

            raise ValueError('bad line {}'.format(l))


    print('(' + '\n:: '.join(reversed(program)) + ' :: nil)')



def format_ref(bindings, i, x):
    if type(x) is tuple:
        a, b = x
        return '(ref_pair {} {})'.format(format_ref(bindings, i, a),
                                         format_ref(bindings, i, b))
    return '(ref_index {})'.format(i - bindings[x] - 1)

def parse_tuples(s):
    l = []
    s = lex_tuple(s)
    while s:
        x, s = parse_tuple_helper(s)
        l.append(x)
    return l

def parse_tuple_helper(s):
    if s[0] == '(':
        x, s = parse_tuple_helper(s[1:])
        if s[0] != ',':
            raise ValueError('expected comma: {}'.format(s))
        y, s = parse_tuple_helper(s[1:])
        if s[0] != ')':
            raise ValueError('expected rparen: {}'.format(s))
        return (x, y), s[1:]
    if s[0].isidentifier():
        return s[0], s[1:]
    raise ValueError('unexpected: {}'.format(s))

def lex_tuple(s):
    return [y for x in s.split() for y in re.split('([(),])', x) if y]

if __name__ == '__main__':
    main()
