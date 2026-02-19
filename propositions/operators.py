# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula

    if is_constant(formula.root):
        p = Formula('p')
        if formula.root == 'T':
            return Formula('|', p, Formula('~', p))
        return Formula('&', p, Formula('~', p))

    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))

    a = to_not_and_or(formula.first)
    b = to_not_and_or(formula.second)

    if formula.root == '&' or formula.root == '|':
        return Formula(formula.root, a, b)
    if formula.root == '->':
        return Formula('|', Formula('~', a), b)
    if formula.root == '+':
        return Formula('|',
                       Formula('&', a, Formula('~', b)),
                       Formula('&', Formula('~', a), b))
    if formula.root == '<->':
        return Formula('|',
                       Formula('&', a, b),
                       Formula('&', Formula('~', a), Formula('~', b)))
    if formula.root == '-&':
        return Formula('~', Formula('&', a, b))
    if formula.root == '-|':
        return Formula('~', Formula('|', a, b))
    raise ValueError('Unknown operator: ' + formula.root)



def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    f = to_not_and_or(formula)

    def conv(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            return g
        if is_unary(g.root):
            return Formula('~', conv(g.first))
        if g.root == '&':
            return Formula('&', conv(g.first), conv(g.second))
        if g.root == '|':
            left = conv(g.first)
            right = conv(g.second)
            return Formula('~',
                           Formula('&',
                                   Formula('~', left),
                                   Formula('~', right)))
        raise ValueError('Unknown operator: ' + g.root)

    return conv(f)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    f = to_not_and(formula)

    def conv(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            return g
        if is_unary(g.root):
            x = conv(g.first)
            return Formula('-&', x, x)
        if g.root == '&':
            x = conv(g.first)
            y = conv(g.second)
            t = Formula('-&', x, y)
            return Formula('-&', t, t)
        raise ValueError('Unknown operator: ' + g.root)

    return conv(f)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    f = to_not_and_or(formula)

    def conv(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            return g
        if is_unary(g.root):
            return Formula('~', conv(g.first))

        a = conv(g.first)
        b = conv(g.second)

        if g.root == '|':
            return Formula('->', Formula('~', a), b)
        if g.root == '&':
            return Formula('~', Formula('->', a, Formula('~', b)))

        raise ValueError('Unknown operator: ' + g.root)

    return conv(f)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    f = to_not_and_or(formula)

    def conv(g: Formula) -> Formula:
        if is_variable(g.root):
            return g
        if is_constant(g.root):
            if g.root == 'F':
                return g
            return Formula('->', Formula('F'), Formula('F'))

        if is_unary(g.root):
            x = conv(g.first)
            return Formula('->', x, Formula('F'))

        a = conv(g.first)
        b = conv(g.second)

        if g.root == '|':
            return Formula('->', Formula('->', a, Formula('F')), b)

        if g.root == '&':
            return Formula('->',
                           Formula('->', a, Formula('->', b, Formula('F'))),
                           Formula('F'))

        raise ValueError('Unknown operator: ' + g.root)

    return conv(f)

