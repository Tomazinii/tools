#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Apr 20 12:31:21 2021

@author: Cedric Luiz de Carvalho
"""

#from prettytable import PrettyTable

import forms as fms

#-----------------------------------------------------------------------------        
class InferRule(): 
    '''
        Inference rules:
        Arguments:
            index: an integer.
            name: the name of the rule.
            nick: the nickname of the rule.
            l_premis: the list of premisses.
            concl: the conclusion.
        '''
 
    def __init__(self, index, name, nick, l_premis, concl):
            self.index = index
            self.name = name
            self.nick = nick
            self.l_premis = l_premis
            self.concl = concl
            
    def __repr__(self):
        lprem =''
        for prem in self.l_premis: 
            if lprem != '':
                lprem += ', '
            lprem += str(prem) 
        return str( lprem + ' '+fms.GlobalConstants.impl+ ' ' + str(self.concl))
    
    def setIndex(self, index): 
            self.index = index
            
    def getIndex(self): 
            return self.index
        
    def setName(self, name): 
            self.oper = name
            
    def getName(self): 
            return self.name

    def setNick(self, name):
            self.nick = nick

    def getNick(self):
            return self.nick
        
    def setPremis(self, l_premis): 
            self.l_premis = l_premis
            
    def getPremis(self): 
            return self.l_premis
        
    def setConclusion(self, concl): 
            self.concl = concl
            
    def getConclusion(self): 
            return self.concl
 
#-----------------------------------------------------------------------------        
def generateInfRuleRepresentation(name, rule):
    '''
        Generate an inference rule.

    :argument name: the name of the rule.
    :argument rule: a rule (list o premisses ana a conclusion).
    :return lPremRepr: a Representation for the premisses,
        conclRepr: a representation for the conclusion.
    '''
    
    # print('name:',name)
    # print('rule:', rule)
    body = rule.get(name)
    premisses = body[0]
    conclusion = body[1]
    # print('premisses:',premisses)
    # print('conclusion:', conclusion)
   
    lPremRepr =[]
    i = 0
    while i < len(premisses):
        r, err_message, form = fms.generate_represent(premisses[i])
        if r:
            lPremRepr.append(form)
            i+=1
        else:
            print('Error generating Inference Rules')
            break

    r, err_message, conclRepr = fms.generate_represent(conclusion)
    if r:
        return lPremRepr, conclRepr
    else:
        print('Error generating Inference Rules')
        return lPremRepr, conclRepr


#-----------------------------------------------------------------------------
def generateInfRules(l_rules):
    '''
        Generate a list of inference rules.

    :argument l_rules: a list of values
    :return rule_table: a table os inference rules
    '''

    rule_table = {} # Table of inference rules
    ir = 0 # An indice for the table
    while ir < len(l_rules):
        nick = l_rules[ir][0]
        name = l_rules[ir][1]
        rule = l_rules[ir][2]
        l_prem, concl = generateInfRuleRepresentation(name,rule)
        rule_table[ir] = InferRule(ir,name,nick,l_prem,concl)
        ir+=1
                
    return rule_table

#-----------------------------------------------------------------------------
def printInfRuleTable(ruleTable):
    '''
        Print a table of inference rule
        :argument ruleTable: a table of inference rules
    '''

    ptable = PrettyTable(["Índice","Nome","Nick","Premissas","Conclusão"])
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
        prs = rule.getPremis()
        lp =''
        for p in prs:
            lp += str(p)+' '
        ptable.add_row([r,rule.getName(),rule.getNick(),lp,str(rule.getConclusion())])
        
    print(ptable)
        
    return ptable
    
#-----------------------------------------------------------------------------
# inference rule = {name: (list_of_premisses, conclusion)}
def createInfRules():
    '''
        Creates a table of inference rules.

    :return rule_table: a table of inference rules

    '''

    # These three lines are not rules in fact, but they are treated as if they are.
    # They are used to introduce and to remove hypothesis.
    ir_adh = {'Ad. Hipótese': (['p'], ('p'))}
    ir_rmh = {'Rem. Hipótese': (['p'], ('p',fms.GlobalConstants.c_if,'q'))}
    ir_absd = {'Red. Absurdo': (['p'], (fms.GlobalConstants.c_not,'p'))}
    ###########################################################################

    ir_ad1 = { 'Adição_1': (['p'],('p',fms.GlobalConstants.c_or,'q') )}
    ir_ad2 = { 'Adição_2': (['p'],('q',fms.GlobalConstants.c_or,'p') )}
    
    ir_simp1 = {'Simplificação_1':  ([('p', fms.GlobalConstants.c_and,'q')],'p')}
    ir_simp2 = {'Simplificação_2':  ([('p', fms.GlobalConstants.c_and,'q')],'q')}

    ir_conj1 = {'Conjunção_1':  (['p','q'],('p', fms.GlobalConstants.c_and,'q'))}
    ir_conj2 = {'Conjunção_2':  (['p','q'],('q',fms.GlobalConstants.c_and,'p'))}
    
    ir_abs = {'Absorção':  ([('p',fms.GlobalConstants.c_if,'q')],('p',fms.GlobalConstants.c_if,('p',fms.GlobalConstants.c_if,'q')))}
    
    ir_mp = {'Modus ponens':  ([('p',fms.GlobalConstants.c_if,'q'),'p'],'q')}
    
    ir_mt = {'Modus tollens':  ([('p',fms.GlobalConstants.c_if,'q'),(fms.GlobalConstants.c_not,'q')],(fms.GlobalConstants.c_not,'p'))}
    
    ir_sd1 = {'Sil. disj._1':  ([('p',fms.GlobalConstants.c_or,'q'),(fms.GlobalConstants.c_not,'p')],('q'))}
    ir_sd2 = {'Sil. disj._2':  ([('p',fms.GlobalConstants.c_or,'q'),(fms.GlobalConstants.c_not,'q')],('p'))}
    
    ir_sh = {'Sil. hipot.':  ([('p',fms.GlobalConstants.c_if,'q'),('q',fms.GlobalConstants.c_if,'r')],('p',fms.GlobalConstants.c_if,'r'))}
    
    ir_dc = {'Dil. constr.':  ([('p',fms.GlobalConstants.c_if,'q'),('r',fms.GlobalConstants.c_if,'s'),('p',fms.GlobalConstants.c_or,'r')],('q',fms.GlobalConstants.c_or,'s'))}
    
    ir_dd = {'Dil. destr.':  ([('p',fms.GlobalConstants.c_if,'q'),('r',fms.GlobalConstants.c_if,'s'),((fms.GlobalConstants.c_not,'q'),fms.GlobalConstants.c_or,(fms.GlobalConstants.c_not,'s'))],((fms.GlobalConstants.c_not,'p'),fms.GlobalConstants.c_or,(fms.GlobalConstants.c_not, 'r')))}

    lInferRules = [('ADHYP', 'Ad. Hipótese', ir_adh),
                ('RMHYP', 'Rem. Hipótese', ir_rmh),
                ('ABsd', 'Red. Absurdo', ir_absd),
                ('ABS', 'Absorção', ir_abs),
                ('ADD1','Adição_1',ir_ad1),
                ('ADD2','Adição_2',ir_ad2),
                ('CONJ1','Conjunção_1',ir_conj1),
                ('CONJ2','Conjunção_2',ir_conj2),
                ('DC','Dil. constr.',ir_dc),
                ('DD','Dil. destr.',ir_dd),
                ('MP','Modus ponens',ir_mp),
                ('MT','Modus tollens',ir_mt),
                ('SD1','Sil. disj._1',ir_sd1),
                ('SD2','Sil. disj._2',ir_sd2),
                ('SH','Sil. hipot.',ir_sh),
                ('SIMP1','Simplificação_1',ir_simp1),
                ('SIMP2','Simplificação_2',ir_simp2)
                ]

    rule_table = generateInfRules(lInferRules)

    return rule_table



#-----------------------------------------------------------------------------# rt = createInfRules()
# printInfRuleTable(rt)
