#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Apr 20 12:31:21 2021

@author: Cedric Luiz de Carvalho
"""

import copy

# from prettytable import PrettyTable

import forms as fms
import equivRules as eqv

#-----------------------------------------------------------------------------        
class PredRule():
    '''
        Equivalence rules:
        Arguments:
            index: an integer.
            name: the name of the rule.
            nick: the nickname of the rule.
            antec: the antecedent.
            consec: the consequent.
    '''

    def __init__(self, index, name, nick, antec, consec):
        self.index = index
        self.name = name
        self.nick = nick
        self.antec = antec
        self.consec = consec

    def __repr__(self):  # Returns the object (a string)
        s = '{self.antec} '+fms.GlobalConstants.impl+' {self.consec}'
        return s.format(self=self)

    def setIndex(self, index):
        self.index = index

    def getIndex(self):
        return self.index

    def setName(self, name):
        self.name = name

    def getName(self):
        return self.name

    def setNick(self, nick):
        self.nick = nick

    def getNick(self):
        return self.nick

    def setAntec(self, antec):
        self.antec = antec

    def getAntec(self):
        return self.antec

    def setConsec(self, consec):
        self.consec = consec

    def getConsec(self):
        return self.consec


#-----------------------------------------------------------------------------
def generatePredRules(l_rules):
    '''
        Generate a list of equivalence rules.

    :argument l_rules: a list of values
    :return rule_table: a table os equivalence rules
    '''

    rule_table = {} # Table of equivalence rules.
    ir = 0 #Index for predicate rules.
    it = 0 #Index for table of predicate rules

    while ir < len(l_rules):
        nick = l_rules[ir][0]
        name = l_rules[ir][1]
        rule = l_rules[ir][2]
        r, msg, antec, consec = eqv.generateEquivRuleRepresentation(name, rule)
        if not r:
            print(f'Predicate rule table could not be generated!')
            print(msg)
            break
        rule_table[it] = PredRule(ir, name, nick + '_lr', antec, consec)
        it += 1
        if name in ["De Morgan Universal", "De Morgan Existencial"]:
            rule_table[it] = PredRule(ir, name, nick + '_rl', consec, antec)
            it += 1
        ir += 1

    return rule_table

#-----------------------------------------------------------------------------

def createPredRules():
    '''
        Creates a table of inference rules.

    :return rule_table: a table of inference rules

    '''
    glob_c = fms.GlobalConstants()

    pr_pu = {'Particularização Universal': ((glob_c.fa, 'x', 'p', ['x']), ('p', ['a']))}

    pr_pe = {'Particularização Existencial': ((glob_c.ex, 'x', 'p', ['x']), ['p', ['a']]  )}

    pr_gu = {'Generalização Universal': ( ('p', ['a']), (glob_c.fa, 'x', 'p', ['x'])  )}

    pr_ge = {'Generalização Existencial': (('p', ['a']), (u'\u2203', 'x', 'p', ['x']))}

    pr_dmu = {'De Morgan Universal': ( (glob_c.c_not,glob_c.fa, 'x','p', ['x']),(glob_c.ex, 'x', glob_c.c_not,'p', ['x'])  )}

    pr_dme = {'De Morgan Existencial':  ((glob_c.c_not,glob_c.ex, 'x','p', ['x']),(glob_c.fa, 'x',glob_c.c_not, 'p', ['x']) )}
    
    lPredRules_inf = [
                ('GU','Generalização Universal',pr_gu),
                ('GE','Generalização Existencial',pr_ge),
                ('PU','Particularização Universal',pr_pu),
                ('PE','Particularização Existencial',pr_pe)
                ]
    lPredRules_equiv = [
        ('DMU', 'De Morgan Universal', pr_dmu),
        ('DME', 'De Morgan Existencial', pr_dme)
    ]

    rule_table_inf = generatePredRules(lPredRules_inf)
    rule_table_equiv = generatePredRules(lPredRules_equiv)

    # eqv.printEquivRuleTable(rule_table)
    return (rule_table_inf,rule_table_equiv)



#-----------------------------------------------------------------------------#
# rt = createPredRules()
#-----------------------------------------------------------------------------
def applyPredRule(formula):
    '''
        Applies an predicate rule to a formula.

    :argument rule: predicate rule.
    :argument formula: a logic formula.
    :return nconcl: a new formula resultinf from the rule application.
    '''

    quants = formula.getQuantifiers()
    scope = formula.getScope() # scope is type Form1, in this case
    nQuants = copy.deepcopy(quants)

    # Exchanges '∃' by '∀' and vice-versa
    for q in nQuants:
        if q.getName() == '∃':
            q.setName('∀')
        else:
            q.setName('∃')

    nScope = scope.getOpnd1() # scope is type Form1
    # The scope is also a FOF (with quantifiers)
    # all quantifier must be gathered in just one list of quantifiers

    if type(nScope) == fms.Fof:
        nQuants =  nQuants + nScope.getQuantifiers()
        nScope = nScope.getScope()

    nf = fms.Fof(nQuants, nScope)
    nform = fms.Form1('∼',nf)

    return True, ' ', nform


# -----------------------------------------------------------------------------
def applyNotPredRule(formula):
    '''
        Applies an predicate rule to a formula.

    :argument rule: predicate rule.
    :argument formula: a logic formula.
    :return nconcl: a new formula resultinf from the rule application.
    '''

    opnd1 = formula.getOpnd1()
    # print(f'opnd1: {opnd1}')
    quants = opnd1.getQuantifiers()
    # print(f'quants: {quants[0]}')
    scope = opnd1.getScope()
    # print(f'scope: {scope}')
    nscope = fms.Form1('∼',scope)
    # print(f'nscope: {nscope}')
    new_quants = copy.deepcopy(quants)
    # print(f'new_quants: {new_quants[0]}')

    for q in new_quants:
        if q.getName() == '∃':
            q.setName('∀')
        else:
            q.setName('∃')

    nform = fms.Fof(new_quants,nscope)
    # print(f'nform: {nform}')

    return True, ' ', nform
