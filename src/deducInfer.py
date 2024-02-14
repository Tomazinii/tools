#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Apr 21 07:30:19 2021

@author: cedric
"""
import copy

# import infRules as inf
import equivRules as eqv
import forms as fms


# #-----------------------------------------------------------------------------
# def mappingGenerate(dic,premissas,linhas):
#     ''' Gera dicionário com mapeamento entre variáveis da regra e das linhas  '''

#     ni = len(premissas)
#     i = 0
#     while i < ni:
#         ndic = fms.unifica(dic,premissas[i],linhas[i])
#         dic.update(ndic)
#         i += 1
#     return dic

#-----------------------------------------------------------------------------
def apply_inference_rule(rule,lines):
    ''' Substitui as variáveis do mapeamento na conclusao da regra  '''

    # for l in lines:
    #     print(f'line: {l} - type: {type(l)}')
    #
    # print(f'rule: {rule}\n\n')

    premisses = rule.getPremis()
    conclusion = rule.getConclusion()
    # for p in premisses:
    #     print(f'premisses: {p} - type: {type(p)}')

    dic = {}
    r, msg, dic = eqv.mappingGenerate(dic,premisses,lines)
    new_conclusion = None
    if r:
        r1, msg1, new_conclusion = eqv.substitue(dic, conclusion)
        return r1, msg1, new_conclusion
    else:
        return r, msg, new_conclusion

#-----------------------------------------------------------------------------
# def applyEquivRule(rule, formula):
#     ''' Substitui fórmula lógica por uma equivalente '''
#
#     dic = {}
#     antec = rule.getAntec()
#     # print(f'Ant: {antec}')
#     consec = rule.getConsec()
#     # print(f'consec: {consec}')
#     # print(f'line: {formula}')
#
#     r, dic = eqv.mappingGenerate(dic,[antec],formula)
#     nconcl = None
#     if r:
#         nconcl = eqv.substitue(dic, consec)
#
#     return r, nconcl

#-----------------------------------------------------------------------------
def getLines(selectdLinesIndices,proveLines):
    '''Gera uma lista com a representação das linhas.
        arg1: lista com os índices das linhas selecionadas
        proveLines: todas as linhas de prova'''
    lines = [] #Lista com as linhas selecionadas

    for f in selectdLinesIndices:
        lines.append(proveLines[f])

    return lines

#-----------------------------------------------------------------------------
def apply(lineIndex,proveLines,rule,selectdLinesIndices):
    ''' Aplica uma regra nas linhas especificadas
        arg1 : índice da linha
        arg2 : lista com as linhas de prova
        arg3 : regra a ser usada
        arg4 : lista com as linhas onde deverá ser aplicada a regra
    '''

    # if  rule == 'adição1' or rule == 'adição2':
    #      print('LER ENTRADA: O QUÊ O USUÁRIO QUER ADICIONAR?')


    selLines = getLines(selectdLinesIndices,proveLines)
    concl = apply_inference_rule(rule,selLines)

    # lineRepr = fms.gera_represent(line_N)
    proveLines.append(concl)
    # print(f'({lineIndex}) {concl}   {selectdLinesIndices} - {rule.getName()}')
    lineIndex += 1
    # return lineIndex, proveLines
    return lineIndex, concl

# #-----------------------------------------------------------------------------
# def applyRule(lineIndex,proveLines,rule,selectdLines):
#     '''Evita a interrupção do programa, emitindo aviso ao usuário em
#        caso da regra não puder ser aplicada nas linhas selecionadas.'''

#     try:
#         lineIndex, proveLines = apply(lineIndex,proveLines,rule,selectdLines)
#     except:
#         print("Essa regra não pode ser aplicada. Tente novamente")

#     return lineIndex, proveLines

#-----------------------------------------------------------------------------
# def applyRule(rule,selectdLines):
#     '''Evita a interrupção do programa, emitindo aviso ao usuário em
#        caso da regra não puder ser aplicada nas linhas selecionadas.'''
#
#     print('Rule: ',rule)
#     for l in selectdLines:
#         print('Selected Line: ',l)
#
#     try:
#         concl = apply_inference_rule(rule,selectdLines)
#     except:
#         print("Essa regra não pode ser aplicada. Tente novamente")
#     return concl

# -----------------------------------------------------------------------------
def is_used_in_line(l, term):

    if type(l) is fms.Form0:
        return False
    if type(l) is fms.Form1:
        return is_used_in_line(l.getOpnd1(), term)
    if type(l) is fms.Form2:
        r1 = is_used_in_line(l.getOpnd1(), term)
        r2 = is_used_in_line(l.getOpnd2(), term)
        return r1 or r2
    if type(l) is fms.Pred:
        args = l.getPredVars()
        if term in args:
            return True
        else:
            return False
    if type(l) is fms.Fof:
        return is_used_in_line(l.getScope(), term)
    else:
        return False


#-----------------------------------------------------------------------------
def check_exist_partic_restrictions(quant_var, new_term, proof_lines):
    '''
            Checks restriction for Existential Particularization:
            (1) if the new term is either a variable or a constant
                it must not be used before

        quant_var: variable to be replaced by the new term
        new_term: term selected to replace the var
        bound_variables: variables bound to quantifiers in the formula
        '''

    # print(f'quant_var: {quant_var}')
    # print(f'new_term: {new_term}')

    r = True
    for l in proof_lines:
        # print(f'l: {l}')
        if is_used_in_line(l, new_term):
            r = False
            break
    # if new_term == quant_var:
    #     return True, ' '
    # elif not r:
    if not r:
        error_msg = 'The new term "' + new_term + '"  ' \
                     '\nhas been used before.\n\n' \
                     'Existential particularization' \
                     '\ncannot be applied!'
        return r, error_msg
    else:
        return r, ' '

# -----------------------------------------------------------------------------
def apply_exist_particularization(quant_var,new_term, first_order_form,proof_lines):

    # print(f'first_order_form: {first_order_form} - type: {type(first_order_form)}')

    quant_name = fms.GlobalConstants.ex
    scope = first_order_form.getScope()
    # print(f'scope: {scope} - type: {type(scope)}')
    quant_vars = first_order_form.getQuantVars()

    r1, msg1 = check_exist_partic_restrictions(quant_var, new_term, proof_lines)
    if r1:
        r2, msg2 = replace_in_scope(quant_name, quant_var, new_term, scope)
        return r2, msg2
    else:
        return r1, msg1


# -----------------------------------------------------------------------------
def check_univer_partic_restrictions(quant_var, new_term, bound_variables):
    '''
        Checks restriction for Universal Particularization:
        (1) If the new term is a variable, it must be free in  predicate scope
          if it is a constant, its ok

    quant_var: variable to be replaced para the new term
    new_term: term selected to replace the var
    bound_variables: variables bound to quantifiers in the formula
    '''

    # print(f'bound_variables: {bound_variables}')
    # print(f'new_term: {new_term}')
    # print(f'quant_var: {quant_var}')

    if is_constant(new_term):
        return True, ' '
    elif is_variable(new_term):  # The new term is a variable
        if new_term == quant_var:
            return True, ' '
        elif new_term not in bound_variables:
            return True, ' '
        else:  # The new  term is a variable bound in predicate
            error_msg = 'The new term  "' + new_term + \
                        '"\nis a variable bound to a quantifier.\n\n' \
                         'Universal particularization ' \
                        '\ncannot be applied!'
            return False, error_msg
    else:  # The new  term is  not a variable nor a constant
        error_msg = 'Wrong new term "' + new_term + '".\n\n' \
                     'Universal particularization ' \
                      '\ncannot be applied.'
        return False, error_msg

# -----------------------------------------------------------------------------
def apply_universal_particularization(quant_var,new_term, first_order_form,proof_lines):

    # print(f'first_order_form: {first_order_form} - type: {type(first_order_form)}')

    quant_name = fms.GlobalConstants.fa
    scope = first_order_form.getScope()
    # print(f'scope: {scope} - type: {type(scope)}')
    quant_vars = first_order_form.getQuantVars()

    r1, msg1 =  check_univer_partic_restrictions(quant_var, new_term, quant_vars)
    if r1:
        r2, msg2 = replace_in_scope(quant_name, quant_var, new_term, scope)
        return r2, msg2
    else:
        return r1, msg1

# -----------------------------------------------------------------------------
def replace_in_scope(quant_name, quant_var,new_term, scope):


    # print(f'scope0: {scope} - type: {type(scope)}')f

    if type(scope) in [fms.Form0,fms.Form]:
        return True, ' '
    elif type(scope) is fms.Form1:
        r, msg = replace_in_scope(quant_name,quant_var,new_term, scope.getOpnd1())
        return r, msg
    elif type(scope) is fms.Pred:
        pred_vars = scope.getPredVars()
        pred_vars[:] = [new_term if x == quant_var else x for x in pred_vars]
        return True, ''
    elif type(scope) is fms.Fof:
        r, msg = replace_in_scope(quant_name,quant_var,new_term,scope.getScope())
        return r, msg
    elif type(scope) is fms.Form2:
        r1, msg1 = replace_in_scope(quant_name,quant_var,new_term,scope.getOpnd1())
        if r1:
            r2, msg2 = replace_in_scope(quant_name,quant_var,new_term,scope.getOpnd2())
            return  r2, msg2
        else:
            return r1, msg1
    else:
        error_msg = 'Wrong new term  "'+new_term+'".' \
                    '\n\nUniversal particularization' \
                    '\ncannot be applied!'
        return False, error_msg

# -----------------------------------------------------------------------------
def is_free_in_formula(formula,var):
    ''' Check if a var is free in the formula.
    formula: a formula
    var: a variable
    Returns true when the var is free in the formula
    '''

    if is_constant(var):
        return False
    if type(formula) is fms.Form1:
        return is_free_in_formula(formula.getOpnd1(),var)
    if type(formula) is fms.Form2:
        r1 = is_free_in_formula(formula.getOpnd1(),var)
        r2 = is_free_in_formula(formula.getOpnd2(),var)
        return r1 or r2
    if type(formula) is fms.Pred:
        pred_vars = formula.getPredVars()
        if var in pred_vars:
            return True
        else:
            return False
    if type(formula) is fms.Fof:
        r = is_free_in_formula(formula.getScope(),var)
        quant_vars = formula.getQuantVars()
        if (var in quant_vars) and r:
            return False
        return r
    else:
        return False

# -----------------------------------------------------------------------------
def is_constant_in_formula(formula,cnst):
    ''' Check if a constant occurs in the formula.
    formula: a formula
    cnst: a constant
    Returns true when the cnst is occurs in the formula
    '''
    # print(f'formula: {formula} - type : {type(formula)}')
    # print(f'cnst: {cnst} - type : {type(cnst)}')

    if not is_constant(cnst):
        return False
    if type(formula) is fms.Form1:
        return is_constant_in_formula(formula.getOpnd1(),cnst)
    if type(formula) is fms.Form2:
        r1 = is_constant_in_formula(formula.getOpnd1(),cnst)
        r2 = is_constant_in_formula(formula.getOpnd2(),cnst)
        return r1 or r2
    if type(formula) is fms.Pred:
        pred_vars = formula.getPredVars()
        if cnst in pred_vars:
            # print(f'var: {cnst} - type : {type(cnst)}')
            return True
        else:
            return False
    if type(formula) is fms.Fof:
        r = is_constant_in_formula(formula.getScope(),cnst)
        # quant_vars = formula.getQuantVars()
        # if (cnst in quant_vars) and r:
        #     return False
        return r
    else:
        return False

# -----------------------------------------------------------------------------
def check_univ_gener_restrictions(selected_term,new_var,q_vars,prem_Hyp,list_of_existential_part_terms):
    ''' Checks for restriction on universal generalization.
            selected_term: the term to be replaced
            q_vars: the bound vars (quantifiers vars)
            previous_free_vars: the constant occurs in an open premiss or hypothesis
            from_ex_part: the new var was deducted from existential particularization

            returns a flag (T or F) and an error message'''

    # UG: the selected term cannot appear in a premiss or in a hypothesis
    # UG: the new var can not be free before or deducted from an existential particularization
    # previous_free_var = False
    # for p in prem_Hyp:
    #     # previous_free_var = previous_free_var or is_free_in_formula(p,selected_term)

    prem_or_hyph_const = False
    for p in prem_Hyp:
        prem_or_hyph_const = prem_or_hyph_const or is_constant_in_formula(p, selected_term)

    # print(f'prem_or_hyph_const: {prem_or_hyph_const}')

    # print(f'list_of_existential_part_terms: {list_of_existential_part_terms}')
    from_ex_part = [p[2] for p in list_of_existential_part_terms if True]
    # print(f'from_ex_part: {from_ex_part}')

    if selected_term in q_vars: # The selected term is a bound variable (a quantifier variable)
        error_msg = 'The selected term "'+selected_term+'" \n\n' \
                    'is a bound variable.\n\n' \
                    'Universal generalization ' \
                    '\ncannot be applied!'
        return False, error_msg
    elif new_var in q_vars:  # The new var is already a bound variable (a quantifier variable)
        error_msg = 'The new var "'+new_var+'"  is\n\n' \
                    'already a bound variable.\n\n' \
                    'Universal generalization ' \
                    '\ncannot be applied!'
        return False, error_msg
    # elif previous_free_var: # The selected term is a free var
    #     error_msg = 'The formula was deducted from a premiss or hypothesis \n' \
    #                 'where the selected term "'+selected_term+'"  was a free variable.\n\n' \
    #                 'Universal generalization cannot be applied!'
    #     return False, error_msg

    elif prem_or_hyph_const: # The selected term is a free var
        error_msg = 'The constant "'+selected_term+'"  occurs\n\n' \
                    ' in a premiss or in a hypothesis. \n\n' \
                    'Universal generalization ' \
                    '\ncannot be applied!'
        return False, error_msg
    elif selected_term in from_ex_part:
        error_msg = 'The selected constant was deducted \n\n' \
                    'from an existential particularization \n\n' \
                    'Universal generalization ' \
                    '\ncannot be applied!'
        return False, error_msg
    else:
        return True, ''

# -----------------------------------------------------------------------------
def apply_univ_gener(form,new_var,term_selected,q_vars,prem_Hyp,deducted_from_ex_part):

   r, msg =  check_univ_gener_restrictions(term_selected,new_var,q_vars,prem_Hyp,deducted_from_ex_part)
   if r:
       form_c = copy.deepcopy(form)
       replace_var_in_form(new_var, term_selected, form_c)

       return True, '', form_c
   else:
        return r, msg, form

# -----------------------------------------------------------------------------
def replace_var_in_form(new_var, term_selected, form):
    # print(f'form: {form}: type(form): {type(form)}')
    if type(form) is fms.Fof:
        replace_var_in_form(new_var, term_selected,form.getScope())
        return
    elif type(form) is fms.Pred:
        vars = form.getPredVars()
        vars[:] = [new_var if x == term_selected else x for x in vars]
        # print(f'vars: {vars}')
        return
    elif type(form) is fms.Form1:
        replace_var_in_form(new_var, term_selected, form.getOpnd1())
        return
    elif type(form) is fms.Form2:
        replace_var_in_form(new_var, term_selected, form.getOpnd1())
        replace_var_in_form(new_var, term_selected, form.getOpnd2())
        return
    else:
        return

# -----------------------------------------------------------------------------
def check_exist_gener_restrictions(new_var, selected_term, q_vars, form_variables):
    ''' Checks for restriction on existential generalization.
        new_var: a var for the new quantifier
        selected_term: the term to be replaced
        q_vars: the bound vars (quantifiers vars)
        form_variables: variables occurring in the formula.

        returns a flag (T or F) and an error message'''

    if new_var == selected_term: # The term selected and the new var are equal
            return True, ''
    elif selected_term in q_vars: # The selected term is a variable of some quantifier
        error_msg = 'The selected variable "'+selected_term+'"  ' \
                    '\nis a bound variable.\n\n' \
                    'Existential generalization ' \
                     '\ncannot be applied!'
        return False, error_msg
    elif new_var in form_variables: # The new var occurs in the predicate
        error_msg = 'The new variable "'+new_var+'"  ' \
                    'has been used in predicate.\n\n ' \
                   'Existential generalization ' \
                    '\ncannot be applied!'
        return False, error_msg
    else:
        return True, ''

# -----------------------------------------------------------------------------
def apply_exist_gener(new_var, q_vars, selected_term, index_terms, form, form_vars):
    ''' Applies existential generalization.
            new_var: a var for the new quantifier
            selected_term: the term to be replaced
            q_vars: the bound vars (quantifiers vars)
            form_variables: variables occurring in the formula.

            returns a flag (T or F) and an error message'''

    # EG: if the term 't' to be replaced in 'p(t)' is a constant, the new variable to replace it
    # must not be appeared in the formula 'p(t)'.

    r, msg = check_exist_gener_restrictions(new_var, selected_term, q_vars, form_vars)


    if r: # If all restrictions are respected, replace the term by the new variable in the formula
        form_c = copy.deepcopy(form)
        replace_var_in_form2(new_var, selected_term, index_terms, form_c)
        return True, msg, form_c
    else:
        return r, msg, form


def is_constant(term):
    # return term in ['a','b','c','d','e']
    return term in fms.GlobalConstants.list_of_consts

def is_variable(term):
    # return term in ['X','Y','Z','W']
    return term in fms.GlobalConstants.list_of_vars

# -----------------------------------------------------------------------------
def replace_var_in_form2(new_var, term_selected,  index_terms, form):
    """
    Replaces the term_selected (a constant) in the positions indicated
    in the list of indexes 'index_terms'. Note that, for instance,
    p(a,a,a) v q(b,a,a) will have index_terms = [1,2,3,5,6]. This list
    indicates the positions of the constant 'a'.

    After processing p(a,a,a), 'index_terms' must be adjusted to [5-3,6-3]
    in order to process q(b,a,a).
    """

    if type(form) is fms.Fof:
        replace_var_in_form2(new_var, term_selected, index_terms, form.getScope())
        return
    elif type(form) is fms.Pred:
        vars = form.getPredVars() #get the arguments of the predicate
        c = vars.count(term_selected) # Number of occurrences of 'term_selected' in the predicate
        pos = 0
        i = 0 # index_terms starts with 1
        while i < len(vars):
            if (vars[i] == term_selected):
                pos += 1
                if pos in index_terms:
                    vars[i] = new_var
                    index_terms.remove(pos)
            i+=1
        # Adjustes index for the next predicate (an occurrence must start at position 1 in all predicates
        index_terms[:] = [x-c  for x in index_terms]
        return
    elif type(form) is fms.Form1:
        replace_var_in_form2(new_var, term_selected,  index_terms, form.getOpnd1())
        return
    elif type(form) is fms.Form2:
        replace_var_in_form2(new_var, term_selected,  index_terms, form.getOpnd1())
        replace_var_in_form2(new_var, term_selected,  index_terms, form.getOpnd2())
        return
    else:
        return

# q =  ['ex', ['X']]
# predicate = ['p', ['X']]
#
# quant_name = q[0]
# quant_var = q[1][0]
# new_term = 'a'
#
# previous_used_constant_list = []
# bound_variables = []
# previous_free_vars_or_pex = []

#
# # r, msg, p = apply_particularization(q, p, previous_used_constant_list, bound_vars, nt,previous_free_vars_or_pex)
#
# r, msg, p = apply_generalization('ex', 'Y', nt, previous_free_vars_or_pex, p)
#
# r, msg = apply_univ_partic(quant_var, new_term, predicate, bound_variables, previous_used_constant_list)
# r, msg = apply_exist_partic(quant_var, new_term, predicate, previous_used_constant_list)
# r, msg = apply_univ_gener(quant_var, quant_name, new_term, predicate, previous_free_vars_or_pex)
# r, msg = apply_exist_gener(quant_var, quant_name, new_term, predicate)
# print(f'r: {r}')
# print(f'msg: {msg}')
# print(f'predicate: {predicate}')
# print(f'previous_used_constant_list: {previous_used_constant_list}')
# print(f'previous_free_vars_or_pex: {previous_free_vars_or_pex}')

