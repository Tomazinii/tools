0#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Apr 21 07:09:47 2021

@author: Cedric Luiz de Carvalho
"""
import copy

#from prettytable import PrettyTable
from itertools import permutations


import forms as fms

# -----------------------------------------------------------------------------


class EquivRule(): 
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
            
    def __repr__(self):         # Returns the object (a string)
        return str(self.antec)+' '+ fms.GlobalConstants.equiv+' '+ str(self.consec)
    
    def setIndex(self, index): 
            self.index = index
            
    def getIndex(self): 
            return self.index
    
    def setName(self, name): 
            self.name = name
            
    def getName(self): 
            return self.name

    def setNick(self, name):
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

# -----------------------------------------------------------------------------


def substitueForm(dic, form):
    '''
        Replaces variable in the form, according with the mapping (dic). Replace
        a variable (the key) by its value. Keys are variables in rules and values
        are variables in formulas.

    :argument dic: a mapping variables/values.
    :argument form: a logic formula.
    :return nform: a formula with names of variables replaced, according to the
        mapping.
    '''
    
    chave = form.getOpnd1()
    # print(f'chave: {chave}')
    if chave in dic:
        value = dic[chave]
        # print(f'value: {value}')
        r = True
        if type(value) is str:
            nform = fms.Form(value)
        else:
            nform = value

        return r, '', nform
    else: # The key is not in dictionary
        r = False
        return r, 'The key is not in dictionary', form

# -----------------------------------------------------------------------------


def substitueForm1(dicCor, form):
    '''
        Changes all variables in a FORM1 object, according to mapping.

    :argument dicCor: the mapping.
    :argument form: the formula.
    :return
        r: an error code (True or False)
        msg: an error message
        nForm: a new Form1 object (a negation of a formula)
        with original variables replaced, according with mapping.
    '''
    oper = form.getOper()
    opnd1 = form.getOpnd1()
    # print(f'opnd1: {opnd1} - type {type(opnd1)}')
        
    if (type(opnd1) is fms.Form1): # Nested negation
        r, msg, nOpnd =substitueForm1(dicCor, opnd1) # r: error code - msg: error message
    else:
        r, msg, nOpnd = substitue(dicCor,opnd1)
    
    nForm = fms.Form1(oper, nOpnd)

    return r, msg, nForm

#-----------------------------------------------------------------------------
def substitue(dicCor, form):
    '''
        Replaces variables, according to the mapping.
        Ex: {p: a, q: b} e p -> q should returns a -> b
        
        * form is the rule e nForm is the proof line

    :argument dicCor: the mapping.
    :argument form: the formula.
    :return
        r: an error code (True or False)
        msg: an error message
        nForm: a new Form* object with original
        variables replaced, according with mapping.
    '''

    # print('substitue')
    # print(f'form: {form} - - type: {type(form)}')

    # for d in dicCor:
        # print(f'dicCor[{d}] : {dicCor[d]}')

    if type(form) is fms.Form0: # Constants
        return True, '', form # returns no error
    # if type(form) is fms.Pred: # Predicates
    #     return True, '', form # returns no error
    # if type(form) is fms.Fof: # First order forms
    #     return True, '', form # returns no error
    if type(form) is fms.Form:  # Atomic propositions
        r, msg, nForm = substitueForm(dicCor, form) # r: error code - msg: error message
        return r, msg, nForm
    elif (type(form) is fms.Form1): # Negations
        r, msg, nForm = substitueForm1(dicCor, form) # r: error code - msg: error message
        return r, msg, nForm
    elif (type(form) is fms.Form2):  # cond., Bicondicional., conj. e disj.
        opnd1 = form.getOpnd1()
        opnd2 = form.getOpnd2()
        oper = form.getOper()
        
        r1, msg, nOpnd1 = substitue(dicCor, opnd1)
        if r1:
            r2, msg, nOpnd2 = substitue(dicCor, opnd2)
            nForm = fms.Form2(nOpnd1, oper, nOpnd2)
            return r2, msg, nForm
        else:
            return r1, msg, form
    else:
        return False, 'The formulas are not unifiable.', form

#-----------------------------------------------------------------------------
def mappingGenerate(dic,premisses,lines):
    '''
        Generates a mapping between variables in rules and rules in proof lines.
        Tests all possible combinations (permutation a lines) of proof lines and
        returns the first with a positive unification.

    :argument dic: previous mapping.
    :argument premisses: premisses of rules.
    :argument lines: proof lines (lines (formulas) selected by user)
    :return
        r: boolean - it is False if none combination os lines unifies with
        premisses,
        msg: an error message
        dic: a new mapping.
    '''

    # for d in dic:
    #     print(f'dic[{d}] : {dic[d]}')
    # for l in lines:
    #     print(f'l: {l} - type: {type(l)} ')
    #     if type(l) is fms.Form2:
    #         print(f'opnd1: {l.getOpnd1()} - type: {type(l.getOpnd1())} ')

    saved_dic = copy.copy(dic)  # Saves the context (dictionary)
    lp = len(premisses)
    if lp != len(lines):
        return False, 'Different number of formulas.',dic
    elif (premisses == []) & (lines == []):
        return True, '', dic
    else:
        perm = permutations(lines)  # Gera todas as combinações possíveis
        for l in perm:
            # print(f'l2: {l} - type: { type(l)} ')
            # if type(l) is fms.Form2:
            #     print(f'opnd1: {l.getOpnd1()} - type:{type(l.getOpnd1())}')
            dic = copy.copy(saved_dic)  # Restaura o cópia salva do contexto (dicionário)
            r = True
            msg = ''
            i = 0
            while i < lp:
                r1, dic = fms.unify(dic, premisses[i], l[i])
                # print(f'l[{i}]: {l[i]} - premisses[{i}]: {premisses[i]} - r: {r1}')
                r = r & r1
                i += 1
            if r:
                return True, '', dic
            else:
                return r, 'Error when unifying formulas.', dic

#----------------------------------------------------------------------------
# f01 = fms.Form('p')
# f02 = fms.Form('a')
# f03 = fms.Form('q')
# f04 = fms.Form('b')

# f11 = fms.Form1(fms.GlobalConstants.c_not,f01)
# f12 = fms.Form1(fms.GlobalConstants.c_not,f02)
# f13 = fms.Form1(fms.GlobalConstants.c_not,f03) # ~ q
# f14 = fms.Form1(fms.GlobalConstants.c_not,f04) # ~ b

# f21 = fms.Form2(f01,fms.GlobalConstants.c_and,f03)
# f22 = fms.Form2(f02,fms.GlobalConstants.c_and,f04)


# f31 = fms.Form2(f01,fms.GlobalConstants.c_or,f03)
# f32 = fms.Form2(f02,fms.GlobalConstants.c_or,f04)

# g01 = fms.Form1(fms.GlobalConstants.c_not,f21)
# g02 = fms.Form1(fms.GlobalConstants.c_not,f22)

# h01 = fms.Form1(fms.GlobalConstants.c_not,f11)
# h03 = fms.Form1(fms.GlobalConstants.c_not,f13) # ~~q
# h04 = fms.Form1(fms.GlobalConstants.c_not,f14) # ~~b

# i31 = fms.Form2(f01,fms.GlobalConstants.c_if,f03)# p -> q
# i32 = fms.Form2(f02,fms.GlobalConstants.c_if,h04)# a -> ~~b

#-----------------------------------------------------------------------------
def applyEquivRule(rule, formula):
    '''
        Applies an equivalence rule to a formula.

    :argument rule: equivalence rule.
    :argument formula: a logic formula.
    :return nconcl: a new formula resultinf from the rule application.
    '''

    dic = {}
    antec = rule.getAntec()
    # print(f'Ant: {antec}')
    consec = rule.getConsec()
    # print(f'consec: {consec}')
    # print(f'line: {formula[0]} - type: {type(formula[0])}')

    r, msg, dic = mappingGenerate(dic, [antec], formula)
    # print(f'r: {r}')
    # if (rule.nick == 'DN') & (type(formula[0]) != fms.Form1):
    #     print(f'Dupla negação invertida: {rule.name}')
    #     dic = {}
    #     r, dic = mappingGenerate(dic, [consec], formula)
    # else:
    #     print( 'ok')
    if r:
        r1, msg1, nconcl = substitue(dic, consec)
        return r1, msg1, nconcl
    else:
        return r, msg, None


# def applyEquivRule(rule, formula):
#     '''
#         Applies an equivalence rule to a formula.
#
#     :argument rule: equivalence rule.
#     :argument formula: a logic formula.
#     :return nconcl: a new formula resultinf from the rule application.
#     '''
#
#
#
#     dic = {}
#     antec = rule.getAntec()
#     # print(f'Ant: {antec}')
#     consec = rule.getConsec()
#     # print(f'consec: {consec}')
#     # print(f'line: {formula[0]} - type: {type(formula[0])}')
#
#     r, msg, dic = mappingGenerate(dic, [antec], formula)
#     # print(f'r: {r}')
#     # if (rule.nick == 'DN') & (type(formula[0]) != fms.Form1):
#     #     print(f'Dupla negação invertida: {rule.name}')
#     #     dic = {}
#     #     r, dic = mappingGenerate(dic, [consec], formula)
#     # else:
#     #     print( 'ok')
#     if r:
#         r1, msg1, nconcl = substitue(dic, consec)
#         return r1, msg1, nconcl
#     else: # Exchange antecedent and consequent of the equivalence rule
#         dic = {}
#         r2, msg2, dic = mappingGenerate(dic, [consec], formula)
#         # print(f'r2: {r}')
#         if r2:
#             r3, msg3, nantec = substitue(dic, antec)
#             # print(f'r3: {r}')
#             return r3, msg3, nantec
#         else:
#             return False, msg2, None

#-----------------------------------------------------------------------------        
def generateEquivRuleRepresentation(name,rule):
    '''
        Generate an equivalence rule representation.

    :argument name: the name of the rule.
    :argument rule: a rule (list o premisses ana a conclusion).
    :return antec: a representarion for the antecedent,
        consec: a representation for the consequent.
    '''
    
    # print('name:',name)
    # print('rule:', rule)
    body = rule.get(name)
    # print('body:', body)
    antecedent = body[0]
    consequent = body[1]

    r, error_message, antec = fms.generate_represent(antecedent)
    if r:
        r1, error_message1, consec = fms.generate_represent(consequent)
        return r1, error_message1, antec, consec
    else:
        return r, error_message, None, None

#-----------------------------------------------------------------------------
def generateEquivRules(l_rules):
    '''
        Generate a list of equivalence rules.

    :argument l_rules: a list of values
    :return rule_table: a table os equivalence rules
    '''
    
    rule_table = {} # Table of equivalence rules.
    ir = 0 #Index for equivalence rules.
    it = 0 #Index for table of equivalence rules

    while ir < len(l_rules):
        nick = l_rules[ir][0]
        name = l_rules[ir][1]
        rule = l_rules[ir][2]
        r, msg, antec, consec = generateEquivRuleRepresentation(name, rule)
        if not r:
            print(f'Equivalence rule table could not be generated!')
            print(msg)
            break
        rule_table[it] = EquivRule(ir, name, nick + '_lr', antec, consec)
        it += 1
        if name not in ["Absorção_c", "Absorção_d", "Comutação_c", "Comutação_d"]:
            rule_table[it] = EquivRule(ir, name, nick + '_rl', consec, antec)
            it += 1
        ir += 1
                
    return rule_table
            
#-----------------------------------------------------------------------------
def printEquivRuleTable(ruleTable):
    '''
       Print a table of inference rule

    :argument ruleTable: a table of inference rules
    '''
    
    ptable = PrettyTable(["Índice", "Nome", "Nick", "Antecedente", "Consequente"])
    # Alinha as colunas
    ptable.align["Índice"] = "l"
    ptable.align["Nome"] = "l"
    ptable.align["Nick"] = "l"
    ptable.align["Premissas"] = "l"
    ptable.align["Conclusão"] = "l"
    # Deixa um espaço entre a borda das colunas e o conteúdo (default)
    ptable.padding_width = 1
    for r in ruleTable:
        rule = ruleTable.get(r)
        antec = str(rule.getAntec())
        consec = str(rule.getConsec())
        ptable.add_row([r,rule.getName(),rule.getNick(),antec, consec])
        
    print(ptable)
        
    return

#-----------------------------------------------------------------------------
# regra de equivalência = {nome: (antecedente, consequente)}
def createEquRules():
    '''
        Creates a table of equivalence rules.

    :return rule_table: a table of equivalence rules
    '''

    # Properties of conjuction

    ir_idem_c = { 'Idempotência_c': (('p',fms.GlobalConstants.c_and,'p'),'p' )}
    ir_com_c = { 'Comutação_c': (('p',fms.GlobalConstants.c_and,'q'),('q',fms.GlobalConstants.c_and,'p') )}
    ir_ass_c = { 'Associação_c': (('p',fms.GlobalConstants.c_and,('q',fms.GlobalConstants.c_and,'r')),(('p',fms.GlobalConstants.c_and,'q'),fms.GlobalConstants.c_and,'r') )}
    ir_ident_ct = {'Identidade_ct': (('p', fms.GlobalConstants.c_and,'⊤'), 'p')}
    ir_ident_cc = {'Identidade_cc': (('p', fms.GlobalConstants.c_and,'⊥'), '⊥')}


    # Properties of disjuction

    ir_idem_d = {'Idempotência_d': (('p', fms.GlobalConstants.c_or, 'p'), 'p')}
    ir_com_d = {'Comutação_d': (('p', fms.GlobalConstants.c_or, 'q'), ('q', fms.GlobalConstants.c_or, 'p'))}
    ir_ass_d = {'Associação_d': (('p', fms.GlobalConstants.c_or, ('q', fms.GlobalConstants.c_or, 'r')), (('p', fms.GlobalConstants.c_or, 'q'), fms.GlobalConstants.c_or, 'r'))}
    ir_ident_dt = {'Identidade_dt': (('p', fms.GlobalConstants.c_or,'⊤'), '⊤')}
    ir_ident_dc = {'Identidade_dc': (('p', fms.GlobalConstants.c_or,'⊥'), 'p')}


    # Properties of conjuction and disjuction

    ir_distr_c = {'Distr._c': (('p', fms.GlobalConstants.c_and, ('q', fms.GlobalConstants.c_or, 'r')), (('p', fms.GlobalConstants.c_and, 'q'), fms.GlobalConstants.c_or, ('p', fms.GlobalConstants.c_and, 'r')))}
    ir_distr_c2 = {'Distr._c2': ( (('p', fms.GlobalConstants.c_and, 'q'), fms.GlobalConstants.c_or, ('r', fms.GlobalConstants.c_and, 's')), (('p', fms.GlobalConstants.c_or, ('r', fms.GlobalConstants.c_and, 's')), fms.GlobalConstants.c_and,('q', fms.GlobalConstants.c_or, ('r', fms.GlobalConstants.c_and, 's'))))}
    ir_distr_d = {'Distr._d': (('p', fms.GlobalConstants.c_or, ('q', fms.GlobalConstants.c_and, 'r')), (('p', fms.GlobalConstants.c_or, 'q'), fms.GlobalConstants.c_and, ('p', fms.GlobalConstants.c_or, 'r')))}
    ir_distr_d2 = {'Distr._d2': ( (('p', fms.GlobalConstants.c_or, 'q'), fms.GlobalConstants.c_and, ('r', fms.GlobalConstants.c_or, 's')), (('p', fms.GlobalConstants.c_and, ('r', fms.GlobalConstants.c_or, 's')), fms.GlobalConstants.c_or,('q', fms.GlobalConstants.c_and, ('r', fms.GlobalConstants.c_or, 's'))))}
    ir_abs_c = {'Absorção_c': (('p', fms.GlobalConstants.c_and, ('p', fms.GlobalConstants.c_or, 'q')), 'p')}
    ir_abs_d = {'Absorção_d': (('p', fms.GlobalConstants.c_or, ('p', fms.GlobalConstants.c_and, 'q')), 'p')}
    ir_dm_c = {'De Morgan_c': ((fms.GlobalConstants.c_not,('p',fms.GlobalConstants.c_and,'q')),((fms.GlobalConstants.c_not,'p'),fms.GlobalConstants.c_or,(fms.GlobalConstants.c_not,'q')))}
    ir_dm_d = {'De Morgan_d': ((fms.GlobalConstants.c_not,('p',fms.GlobalConstants.c_or,'q')),((fms.GlobalConstants.c_not,'p'),fms.GlobalConstants.c_and,(fms.GlobalConstants.c_not,'q')))}


    # Properties of conditional


    ir_dcond = {'Condicional': (('p', fms.GlobalConstants.c_if, 'q'),((fms.GlobalConstants.c_not, 'p'), fms.GlobalConstants.c_or, 'q'))}
    ir_ncond = {'Neg. condicional': ((fms.GlobalConstants.c_not, ('p', fms.GlobalConstants.c_if, 'q')), ('p', fms.GlobalConstants.c_and, (fms.GlobalConstants.c_not, 'q')))}
    ir_cp = {'Contrapositiva': (('p', fms.GlobalConstants.c_if, 'q'), ((fms.GlobalConstants.c_not, 'q'), fms.GlobalConstants.c_if, (fms.GlobalConstants.c_not, 'p')))}
    ir_distr_cond_c = {'Distr._cc': (('p', fms.GlobalConstants.c_if, ('q', fms.GlobalConstants.c_and, 'r')), (('p', fms.GlobalConstants.c_if, 'q'), fms.GlobalConstants.c_and, ('p', fms.GlobalConstants.c_if, 'r')))}
    ir_distr_DEF_COND = {'Distr._dc': (('p', fms.GlobalConstants.c_if, ('q', fms.GlobalConstants.c_or, 'r')), (('p', fms.GlobalConstants.c_if, 'q'), fms.GlobalConstants.c_or, ('p', fms.GlobalConstants.c_if, 'r')))}
    ir_abs_cond = {'Absorção_cd': (('p', fms.GlobalConstants.c_if, ('p', fms.GlobalConstants.c_and, 'q')), ('p', fms.GlobalConstants.c_if, 'q'))}
    ir_expImp = {'Exportação-importação.': ((('p', fms.GlobalConstants.c_and, 'q'), fms.GlobalConstants.c_if, 'r'), ('p', fms.GlobalConstants.c_if, ('q', fms.GlobalConstants.c_if, 'r')))}
    ir_tp = {'Troca premissas': (('p', fms.GlobalConstants.c_if, ('q', fms.GlobalConstants.c_if, 'r')), ('q', fms.GlobalConstants.c_if, ('p', fms.GlobalConstants.c_if, 'r')))}


    # Properties of Bicondicional

    ir_Bicondicional1 = { 'Bicondicional_1': (('p',fms.GlobalConstants.c_iff,'q'),(('p',fms.GlobalConstants.c_if,'q'),fms.GlobalConstants.c_and,('q',fms.GlobalConstants.c_if,'p')))}
    ir_Bicondicional2 = { 'Bicondicional_2': (('p',fms.GlobalConstants.c_iff,'q'),(((fms.GlobalConstants.c_not,'p'),fms.GlobalConstants.c_or, 'q'),fms.GlobalConstants.c_and ,((fms.GlobalConstants.c_not,'q'),fms.GlobalConstants.c_or, 'p')))}
    ir_Bicondicional3 = { 'Bicondicional_3': (('p',fms.GlobalConstants.c_iff,'q'),(('p',fms.GlobalConstants.c_and, 'q'),fms.GlobalConstants.c_or, ((fms.GlobalConstants.c_not,'p'),fms.GlobalConstants.c_and, (fms.GlobalConstants.c_not,'q'))))}

    # Equivalence rules

    ir_dn = {'Dupla negação': ((fms.GlobalConstants.c_not, (fms.GlobalConstants.c_not, 'p')), 'p' )}
    ir_compl1 = {'Complemento_1': (('p', fms.GlobalConstants.c_or, (fms.GlobalConstants.c_not, 'p')), '⊤')}
    ir_compl2 = {'Complemento_2': (('p', fms.GlobalConstants.c_and, (fms.GlobalConstants.c_not, 'p')), '⊥')}
    ir_compl3 = {'Complemento_3': ((fms.GlobalConstants.c_not,  '⊥'), '⊤')}
    ir_compl4 = {'Complemento_4': ((fms.GlobalConstants.c_not, '⊤'), '⊥')}
    ir_Clavius = {'Clavius': ('p', ((fms.GlobalConstants.c_not, 'p'),fms.GlobalConstants.c_if,'p'))}



    lEquivRules = [('ABS_cond', 'Absorção_cd', ir_abs_cond),
                ('ABS_c', 'Absorção_c', ir_abs_c),
                ('ABS_d', 'Absorção_d', ir_abs_d),
                ('ASSOC_c', 'Associação_c', ir_ass_c),
                ('ASSOC_d','Associação_d',ir_ass_d),
                ('Bic1', 'Bicondicional_1', ir_Bicondicional1),
                ('Bic2', 'Bicondicional_2', ir_Bicondicional2),
                ('Bic3', 'Bicondicional_3', ir_Bicondicional3),
                ('Clavius', 'Clavius', ir_Clavius),
                ('COM_c', 'Comutação_c', ir_com_c),
                ('COM_d','Comutação_d',ir_com_d),
                ('COMPL_c', 'Complemento_1', ir_compl1),
                ('COMPL_d', 'Complemento_2', ir_compl2),
                ('COMPL_F', 'Complemento_3', ir_compl3),
                ('COMPL_V', 'Complemento_4', ir_compl4),
                ('COND','Condicional',ir_dcond),
                ('CP','Contrapositiva',ir_cp),
                ('DISc', 'Distr._c', ir_distr_c),
                ('DISTc2', 'Distr._c2', ir_distr_c2),
                ('DISTd', 'Distr._d', ir_distr_d),
                ('DISTd2', 'Distr._d2', ir_distr_d2),
                ('DISTcc', 'Distr._cc', ir_distr_cond_c),
                ('DISTdc', 'Distr._dc', ir_distr_DEF_COND),
                ('DM_c', 'De Morgan_c', ir_dm_c),
                ('DM_d', 'De Morgan_d', ir_dm_d),
                ('DN', 'Dupla negação', ir_dn),
                ('E_I','Exportação-importação.',ir_expImp),
                ('IDEMP_c', 'Idempotência_c', ir_idem_c),
                ('IDEMP_d', 'Idempotência_d', ir_idem_d),
                ('IDENT_cc', 'Identidade_cc', ir_ident_cc),
                ('IDENT_ct', 'Identidade_ct', ir_ident_ct),
                ('IDENT_dc', 'Identidade_dc', ir_ident_dc),
                ('IDENT_dt', 'Identidade_dt', ir_ident_dt),
                ('NEG_COND','Neg. condicional',ir_ncond),
                ('TP', 'Troca premissas', ir_tp)
                ]

    rule_table = generateEquivRules(lEquivRules)

    return rule_table

# #-----------------------------------------------------------------------------
# def applyEquiv(rule,formula):
#     '''
#        Applies an equivalence rule to a formula.
#
#     :argument rule: an equivalence rule.
#     :argument formula: a formula
#
#     :return result: the new resultinf formula.
#     '''
#     result = applyEquivRule(rule, formula)
#     print(f'{rule.getIndex()} - {rule.getName()} ===> {result}')
#
#     return result
#
#
# #-----------------------------------------------------------------------------
# def applyRule():
#     '''Evita a interrupção do programa, emitindo aviso ao usuário em
#        caso da regra não puder ser aplicada nas linhas selecionadas.'''
#
#     rt = createEquRules()
#     printEquivRuleTable(rt)
#
#     f = ('a',fms.GlobalConstants.c_and,'b')
#
#     r, error_message, formula =  fms.generate_represent(f)
#
#     print('Digite o número da regra:')
#     rule = rt[int(input())]
#
#     try:
#         applyEquiv(rule,formula)
#     except:
#         print("Essa regra não pode ser aplicada. Tente novamente")
#
#     return

#-----------------------------------------------------------------------------
# rt = createEquRules()
# printEquivRuleTable(rt)


