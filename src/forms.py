#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Apr 20 10:37:10 2021

@author: Cedric Luiz de Carvalho
"""

import copy


class GlobalConstants():

    c_not = u'\u223C' # Conective NOT (∼)
    c_and = u'\u2227'  # Conective AND (∧)
    c_or = u'\u2228'  # Conective OR (∨)
    c_xor = u'\u22BB'  # Conective XOR (⊻)
    c_if = u'\u2192' # Conective IF (→)
    c_iff = u'\u2194'  # Conective IF and only IF (↔)
    c_ass = u'\u22A2' # Conective ASSERTION (⊢)
    c_equiv = u'\u21D4' # Conective ASSERTION (⇔)
    c_sh_up = u'\u2191'  # Conective SHEFFER UP (↑)
    c_sh_down = u'\u2193'  # Conective SHEFFER DOWN (↓)
    fa = u'\u2200' # ForAll operator ('∀')
    ex = u'\u2203' # There exists operator ('∃')
    true = u'\u22A4' # Constant True ('⊤')
    false = u'\u22A5' # Constant False ('⊥')
    impl = u'\u21D2' # Implication operator ('⇒')
    equiv = u'\u21D4' # Bi-implication operator ('⇔')
    cnf = 'CNF'
    dnf = 'DNF'

    list_of_vars = ['x', 'y', 'z', 'w']
    list_of_special_consts = [true, false, cnf, dnf]
    list_of_consts = ['a', 'b', 'c', 'd', 'e']
    list_of_terms = list_of_vars + list_of_consts
    list_of_quants = [fa,ex ]
    list_of_functs = ['p', 'q', 'r', 's', 't', 'u']
    list_of_cnecs =  [c_and,c_or,c_if,c_iff]
    list_of_all_conecs = [c_not]+list_of_cnecs

class Form:
    '''
    Defines a class for logic formulas with only propositional symbols.
    An atomic proposition: a letter from the end of alphabet (p,q,r,...)

    Argument: opnd1
    '''
    def __init__(self, opnd1):  
        self.opnd1 = opnd1

    def __eq__(self, other):
        if type(other) is not Form:
            return False
        else:
            return self.opnd1 == other.opnd1
        
    def __str__(self):         # Form to string
        return '{self.opnd1}'.format(self=self)
 
    def setOpnd1(self, opnd1): # Sets a new operand (a value)
        self.opnd1 = opnd1 
            
    def getOpnd1(self): # Gets the operand of a Form
        return self.opnd1 
# -----------------------------------------------------------------------------


class Form0(Form):
    '''
    Defines the constants T (tautology) and
    C (contradiction)

    Extends Form.

    Argument: opnd1
    '''

    def __init__(self, opnd1):
       Form.__init__(self, opnd1)

    def __eq__(self, other):  # Checks equivalence of two Form1 objects
        if type(other) is not Form0:  # The other object must be Form0
            return False
        else:  # Operands of both objects must be igual
            return self.opnd1 == other.opnd1

    def __str__(self):  # Form0 to string
       return '{self.opnd1}'.format(self=self)

class Form1(Form): 
    '''
    Defines negation of a proposition.
    The operation must always be (~).
    The operand must be a logic formula.

    Extends Form.

    Argument: opnd1
    '''
    
    oper = GlobalConstants.c_not    # Negation is an operation with just one argument
    
    def __init__(self, oper, opnd1):  
        Form.__init__(self, opnd1)

    def __eq__(self, other): # Checks equivalence of two Form1 objects
        if type(other) is not Form1: # The other object must be Form1
            return False
        else: # Operands of both objects must be igual
            eqs0 = (self.oper == other.oper)
            eqs1 = (self.opnd1 == other.opnd1)
            return eqs0 & eqs1
        
    def __str__(self):         # Form1 to string
        if type(self.opnd1) is Form2: # Negation of a Form2 object is printed between parenthesis
            return GlobalConstants.c_not+'({self.opnd1})'.format(self=self)
        else:
            return GlobalConstants.c_not+'{self.opnd1}'.format(self=self)
    
            
    def getOper(self): 
        return self.oper    # Gets operator (~)
    
# -----------------------------------------------------------------------------

class Form2(Form1): 
    '''
    Defines composed formulas, with the operands connected
    by one of the operators (^ v -> <->).

    Extends Form1.

    Arguments: opnd1 and opnd2
    '''

    def __init__(self, opnd1, oper, opnd2):
            Form1.__init__(self, oper, opnd1 )
            if oper in GlobalConstants.list_of_cnecs:
                self.oper = oper
                self.opnd2 = opnd2
            else:
                print('Error in defining Form2 class')

    def __eq__(self, other):
        if type(other) is not Form2: # The other object must be Form2
            return False
        else:
            eqs = (self.oper == other.oper) & (self.opnd1 == other.opnd1) & (self.opnd2 == other.opnd2)
            return eqs

    def __str__(self):       # Form2 to string
    
            if (type(self.opnd1) is Form2) & (type(self.opnd2) is Form2):
                return '({self.opnd1}) {self.oper} ({self.opnd2})'.format(self=self)
            elif type(self.opnd1) is Form2:
                return '({self.opnd1}) {self.oper} {self.opnd2}'.format(self=self)
            elif type(self.opnd2) is Form2:
                return '{self.opnd1} {self.oper} ({self.opnd2})'.format(self=self)
            else:
                return '{self.opnd1} {self.oper} {self.opnd2}'.format(self=self)
        
    def setOper(self, oper): 
            self.oper = oper
            
    def getOper(self): 
            return self.oper
        
    def setOpnd2(self, opnd2): 
            self.opnd2 = opnd2
            
    def getOpnd2(self): 
            return self.opnd2

    def haveJustOneOper(self):
        op = self.oper

        opnd1 = self.getOpnd1()
        opnd2 = self.getOpnd2()
        if (type(opnd1) is Form2) and (type(opnd2) is Form2):
             if op == opnd1.haveJustOneOper() and op == opnd2.haveJustOneOper():
                return op
             else: return 'NO_OP'
        elif isAtomic(opnd1) and type(opnd2) is Form2:
            if op == opnd2.haveJustOneOper():
                return op
            else: return 'NO_OP'
        elif isAtomic(opnd2) and type(opnd1) is Form2:
            if op == opnd1.haveJustOneOper():
                return op
            else: return 'NO_OP'
        if isAtomic(opnd1) and isAtomic(opnd2):
            return op
        else:
            return 'NO_OP'



# -----------------------------------------------------------------------------
class Quant():
    '''
    Defines a quantifier, either universal (fa) or existential (ex.
    Arguments: name an var
    '''

    def __init__(self, name,variable):

        self.name = name
        self.variable = variable

    def __str__(self):  # Quant to string
        return self.name+self.variable

    def __eq__(self, other):
        if type(other) is not Quant:  # The other object must be Quant
            return False
        else:
            if (self.name == other.name) and (self.variable == other.variable):
                return True
            else:
                return False

    def getName(self):
        return self.name

    def setName(self,name):
        self.name = name

    def getVar(self):
        return self.variable

# -----------------------------------------------------------------------------
class Pred(Form):
    '''
    Defines predicates.

    Extends Form.

    Argument: name - a Form object
              variables - a list of variables
    '''

    def __init__(self, opnd1, variables):
        Form.__init__(self, opnd1)

        self.variables = variables

    def __str__(self):  # Pred to string
        vrs = ",".join(self.variables)
        s_pred = str(self.opnd1)+'('+vrs+')'
        return s_pred.format(self=self)

    def __eq__(self, other):
        if type(other) is not Pred: # The other object must be Pred
            return False
        else:
            eqs = (self.opnd1 == other.opnd1) &  (self.variables == other.variables)
            return eqs

    def getPredName(self):
        return self.opnd1

    def getPredVars(self):
        return self.variables

    def setPredVars(self, vars):
        self.variables = vars
        return
    #
    # def removeQuantifier(self, quant):
    #     self.quantifiers.remove(quant)
    #     return
    #
    # def addQuantifier(self, quant):
    #     self.quantifiers.append(quant)
    #     return

# -----------------------------------------------------------------------------
class Fof(Form):
    '''
    Defines First Order Formulas

    Argument: lquants - a list of quantifier
              scope - the scope of the Fof
    '''

    def __init__(self, quantifiers, scope):

        self.quantifiers = quantifiers
        self.scope = scope

    def __str__(self):  # Pred to string
        lqt = ''
        for qt in self.quantifiers:
            lqt = lqt + str(qt)
        if type(self.scope) is Form2:
            s_form = lqt+'('+str(self.scope)+')'
        else:
            s_form = lqt+str(self.scope)
        return s_form.format(self=self)

    def __eq__(self, other):
        if type(other) is not Fof: # The other object must be Fof
            return False
        else:
            eqs = (self.quantifiers == other.quantifiers) &  (self.scope == other.scope)
            return eqs


    def getQuantifiers(self):
        return self.quantifiers

    def removeQuantifier(self,quant):
        self.quantifiers.remove(quant)
        return

    def insertQuantifier(self, quant):
        self.quantifiers.insert(0,quant)
        return

    def getScope(self):
        return self.scope

    def setScope(self,new_scope):
        self.scope = new_scope
        return

    def getQuantVars(self):
        l_quants = self.getQuantifiers()
        l_var_quants = []
        for q in l_quants:  # Gets variable names of all quantifiers
            varq = q.getVar()
            l_var_quants.append(varq)
        return l_var_quants


# -----------------------------------------------------------------------------


# f02 = Form('a')
# f03 = Form('q')
# f04 = Form('b')
#
# f11 = Form1('~',f01)
# f13 = Form1('~',f03)
# #
# f21 = Form2(f01,'v',f11)
# f22 = Form2(f03,'v',f13)
#
# -----------------------------------------------------------------------------
def new_Formula(args):
    '''
      Creates a new logic formula.

    :param args: a logic formula (a string).
    :return: a logic formula object - Form*
    '''

    if args[0] == Glob_cnts.c_not:
        form0 = new_Formula(args[1])
        form = Form1(GlobalConstants.c_not, form0)
    elif len(args) > 2 and args[1] in  list_of_cnecs:  #['^','v','->',',<->']
        form0 = new_Formula(args[0])
        form1 = new_Formula(args[2])
        form = Form2(form0, args[1], form1)
    else:
        form = Form(args[0])
           
    return form

# -----------------------------------------------------------------------------

def updateDic(dic,index,value):
    '''
        Updates variable mapping. If a variable is in the dictionary
        already, its value must be the same new value to be associated
        to it, otherwise unification fails.

    :param dic: the variables/values mapping.
    :param index: the key (variable name).
    :param value: value
    :return unify: a boolean, dic: variable mapping.
    '''
    # print(f'index: {index} - value: {value}')

    if index in dic:
        if dic[index] != value:
            unify = False
        else:
            unify = True
    else:
        dic[index] = value 
        unify = True
    return unify, dic

# -----------------------------------------------------------------------------
def unify(initDic,formula1,formula2):
    '''
        Checks if two logic forms unify, updating the variable mapping.

        :param initDic: the variables/values mapping.
        :param formula1: A formula to be unified.
        :param formula2: A formula to be unified.
        :return (1) A boolean (False, if formulas do not unify).
                (2) The updated mapping (a dictionary).

                Ex.: (p -> q) e (a -> b) produces the mapping {p:a, q:b}
    '''
    # print(f'formula1: {formula1} <{type(formula1)}>, formula2: {formula2}<{type(formula2)}>')

    if (type(formula1) is Form0) & (type(formula2) is Form0):  # Constants
        r_unify = formula1.getOpnd1() == formula2.getOpnd1()
        return r_unify, initDic
    elif (type(formula1) is Form) & (type(formula2) is Form):  # Atomic formulas
        r_unify, newDic = updateDic(initDic, formula1.getOpnd1(), formula2.getOpnd1())
        return True & r_unify, newDic
    elif(type(formula1) is Form) & (type(formula2) is Form0):  # A variable and a constant (T or C)
        r_unify, newDic = updateDic(initDic, formula1.getOpnd1(), formula2)
        return True & r_unify, newDic
    elif (type(formula1) is Form) & (type(formula2) is Form1):  # p => ~a produces  {p:~a}
        r_unify, newDic = updateDic(initDic,formula1.getOpnd1(),formula2)
        return True & r_unify, newDic
    elif (type(formula1) is Form) & (type(formula2) is Form2):  # p => a ^ b produces  {p:a ^ b}
        r_unify, newDic = updateDic(initDic,formula1.getOpnd1(),formula2)
        return True & r_unify, newDic
    elif (type(formula1) is Form1) & (type(formula2) is Form1):  # Negations
        r, newDic = unify(initDic, formula1.getOpnd1(),formula2.getOpnd1() )
        return r & True, newDic
    # inserted 22/11/2023
    elif (type(formula1) is Form1) & (type(formula2) is Form):  # ~p and p do not unify
        f1_opnd1 = formula1.getOpnd1() # Remove negation from formula 1
        if f1_opnd1 == formula2:
            return False, initDic
        else:
            r, newDic = unify(initDic, f1_opnd1, formula2)  # ~p => A produces {p:~A}
            return r & True, newDic
    ###################
    elif type(formula1) is Form1:
        f1_opnd1 = formula1.getOpnd1() # Remove negation from formula 1
        nformula2 = Form1(GlobalConstants.c_not,formula2) #  Denies formula 2
        if type(f1_opnd1) is Form1: # ~~p => A produces {p:~~A}
            r, newDic = unify(initDic, f1_opnd1.getOpnd1(),  Form1(GlobalConstants.c_not,nformula2))
        else: # {~p => ~A}
        # print(f'f1.opnd1: {formula1.getOpnd1()} - {type(formula1.getOpnd1())}>, f2.opnd1: {formula2.getOpnd1()}- {type(formula2.getOpnd1())}>')
            r, newDic = unify(initDic, f1_opnd1,nformula2 )
        return r & True, newDic

    # elif (type(formula1) is Form1) & (type(formula2) is Form):  # ~p => a produces {p:~a}
    #     nformula2 = Form1(GlobalConstants.c_not,formula2) #  Denies formula 2
    #     f1_opnd1 = formula1.getOpnd1()
    #     if type(f1_opnd1) is Form1: # ~~p => a produces {p:~~a}
    #         r, newDic = unify(initDic, f1_opnd1.getOpnd1(),  Form1(GlobalConstants.c_not,nformula2))
    #     else:
    #     # print(f'f1.opnd1: {formula1.getOpnd1()} - {type(formula1.getOpnd1())}>, f2.opnd1: {formula2.getOpnd1()}- {type(formula2.getOpnd1())}>')
    #         r, newDic = unify(initDic, formula1.getOpnd1(),nformula2 )
    #     return r & True, newDic
    # elif (type(formula1) is Form1) & (type(formula2) is Form2):  # ~p  => q op r produces {p: ~(q op r)}
    #     print('aqui')
    #     nformula2 = Form1(GlobalConstants.c_not,formula2) #  Denies formula 2
    #     f1_opnd1 = formula1.getOpnd1()
    #     r, newDic = unify(initDic, f1_opnd1, nformula2)
    #     return r & True, newDic
    elif (type(formula1) is Form2) & (type(formula2) is Form2):
        if formula1.getOper() == formula2.getOper(): # cond., bicond., conj. e disj.
            r1, newDic = unify(initDic, formula1.getOpnd1(),formula2.getOpnd1() )
            # print(f'f1.opnd2: {formula1.getOpnd2()} - {type(formula1.getOpnd2())}>, f2.opnd2: {formula2.getOpnd2()} - {type(formula2.getOpnd2())}>')
            r2, newDic2 = unify(newDic, formula1.getOpnd2(),formula2.getOpnd2() )
            # print(f'conclui - r ={ r1 & r2}')
            return r1 & r2 & True, newDic2
        else:
            return False, initDic
    elif (type(formula1) is Form) & (type(formula2) is Pred):
        r_unify, newDic = updateDic(initDic, formula1.getOpnd1(), formula2)
        return True & r_unify, newDic
    elif (type(formula1) is Form) & (type(formula2) is Fof):
        r_unify, newDic = updateDic(initDic, formula1.getOpnd1(), formula2)
        return True & r_unify, newDic
    else:
        return False, initDic

# -----------------------------------------------------------------------------
def index_form(pos, form):
    '''
    Transform a formula into a list of subformulas in string format.

    :param form: a logic formula (string)
    :return: a list of subformulas, converted to string
    '''
    # print(f'>>>>Form to index: {form} = len(form): {len(str(form))}')
    # print(f'Initial pos: {pos}')
    # s_form = str(form)
    # i = 0
    # while i < len(s_form):
    #     print(f's_form[{i}]: {s_form[i]}')
    #     i+= 1

    # if type(form) in [Form, Form0, Pred, Fof]:
    if type(form) in [Form, Form0, Pred]:
        return [(pos, form)]
    elif type(form) is Fof:
        scope = form.getScope()
        return(index_form(pos+3,scope))
    elif type(form) is Form1:
        opnd1 = form.getOpnd1()
        if type(opnd1) is Form2:
            f_opnd1 = index_form2(pos+2, opnd1) #  (  +1
            # print(f'f_opnd1_Form2: {f_opnd1}')
            return [(pos,form)] + f_opnd1
        else:
            f_opnd1 = index_form(pos+1, opnd1)
            # print(f'f_opnd_Form1: {f_opnd1}')
            return [(pos,form)] + f_opnd1
    elif type(form) is Form2:
        return index_form2(pos,form)
    else:
        return []

# -----------------------------------------------------------------------------
def index_form2(pos, form):
    '''
    Transform a formula Form2 into a list of subformulas in string format.

    :param form: a logic formula (string)
    :return: a list of subformulas, converted to string
    '''

    l_oper = len(form.getOper())  # length of operator
    # An operator has an space before and after it, so its
    #  lenght must be incremented by 2
    l_oper += 2
    # print(f'len oper: {l_oper}')
    # print(f'pos: {pos}')

    opnd1 = form.getOpnd1()
    opnd2 = form.getOpnd2()
    # print(f'opnd1: {opnd1}')
    # print(f'opnd2: {opnd2}')

    initial_pos = copy.copy(pos) # initial position of the form
    len_opnd1 = len(str(opnd1))  # length of operand 1
    # print(f'len_opnd1: {len_opnd1}')
    if type(opnd1) is Form1:  # ~ opnd1 oper opnd2
        f_opnd1 = index_form(pos, opnd1)
        # print(f'f_opnd_Form1: {f_opnd1}')
    elif type(opnd1) is Form2:  # ( X oper Y ) oper opnd2
        # pos must be incremented by 1 to count open parenthesis
        f_opnd1 = index_form2(pos+1, opnd1)
        # A Form2 as operand of another Form2 needs close parenthesis
        # so, its lenght must be incremented by 2
        len_opnd1 += 2
        # print(f'len opnd1: {len_opnd1}')
    else:
        # f_opnd1 = [(pos, str(opnd1))]
        f_opnd1 = [(pos, opnd1)]

    if type(opnd2) is Form1:  # opnd1 oper ~ opnd2
        # The initial position of the second operand is
        # position of the first operand +
        # the length of the  first operand +  the length of operator + 2 + 1
        # (it was previously has been added by 2 - so it is not needed
        # to be incremented here)
        # len_opnd counts the number of characters, but position starts at 0
        pos_operand2 = initial_pos + (len_opnd1-1) + l_oper+1
        f_opnd2 = index_form(pos_operand2, opnd2)
        # print(f'pos_operand2: {pos_operand2}')
    elif type(opnd2) is Form2:  # opnd1 oper (Y oper Z)
        # The initial position of the second operand is
        # position of the first operand +
        # the length of the  first operand +  the length of operator
        # (it was previously has been added by 2 - so it is not needed
        # to be incremented here) + 1 + 1 (to account an open parenthesis)
        # len_opnd1 accounts for the number of characters, but position starts at 0
        # so it must be decremented by 1

        # print(f'pos of opnd1 in form2: {pos}')

        pos_operand2 = initial_pos + (len_opnd1-1) + l_oper+ 2
        f_opnd2 = index_form2(pos_operand2, opnd2)
    else:
        # print(f'pos of opnd1 : {pos}')
        pos_oper2 = initial_pos + len_opnd1 + l_oper
        # f_opnd2 = [(pos_oper2, str(opnd2))]
        f_opnd2 = [(pos_oper2, opnd2)]

    # f_opnd2 = index_form(pos_oper2, opnd2)

    # print(f'f_opnd2: {f_opnd2}')
    # return [(pos,str(form))] + f_opnd1 + f_opnd2
    return [(pos, form)] + f_opnd1 + f_opnd2


# ----------------------------------------------------------------------------

# f01 = Form('p')
# f02 = Form('a')
# f03 = Form('q')
# f04 = Form('b')
#
# f11 = Form1('~',f01)
# f13 = Form1('~',f03)
# #
# f21 = Form2(f01,'v',f02)
# f22 = Form2(f03,'v',f13)
#
# f31 = Form2(f21,'^',f03)
#
# f51 = Form2(f03,'^',Form0('T'))
# f61 = Form2(f03,'->',Form0('T'))
#
# f71 = Form2(f21,'<->',f61)
#
# lforms = index_form(0,f71)
# print(f71)
# print(lforms)
#
# i = 0
# for f in lforms:
#     print(f)

# r, dic = unify({}, f21, f22)
# print(f'r: {r}')
#
# for d in dic:
#     print(f'dic[{d}] : {dic[d]}')
#
# print(f'r : {r}')
#
# f31 = Form2(f01,'v',f03)
# f32 = Form2(f02,'v',f04)
#
# g01 = Form1('~',f21)
# g02 = Form1('~',f22)


# r, dic = unify({}, f51, f51)# for d in dic:
# for d in dic:
#     print(f'dic[{d}] : {dic[d]}')
# print(f'r: {r}')

# q1 = Quant('∀','x')
# q2 = Quant('∃','y')
# print(f'q01: {q1}')
# print(f'q02: {q2}')
# f01 = Form('p')
# vars1 = ['x','y']
# p01 = Pred(f01,vars1)
#
# p02 = Pred(f01,vars1)
# print(f'p01: {p01}')
# print(f'equals: {p01 == p02}')
#
# f02 = Form('q')
# vars2 = ['y']
# p02 = Pred(f02,vars2)
# print(f'p02: {p02}')
#
# p03 = Form2(p01, '^', p02)
# fof01 = Fof([q1,q2],p01)
# print(f'fof01: {fof01}')
#
# fof02 = Fof([q1,q2],p03)
# print(f'fof01: {fof02}')
#
#
# f11 = Form2(f01,'v',f02)
# p11 = Form2(p01,'v',p02)
#
# r, dic = unify({}, f11, p11)
# print(f'r: {r}')
# for d in dic:
#     print(f'dic[{d}] : {dic[d]}')


# -----------------------------------------------------------------------------


def print_mapeamento(dic):
    print("contexto: {")
    for key, value in dic.items():
        print('(', key, ': ', value,')') 
    print("}")

# -----------------------------------------------------------------------------
def generate_represent(form):
    '''
        Generates a representation for a formula (a string).
        Produces FORM* objects.

    :param form: a formula (in tuple format)
    :return (1) r: a boolean (False if representation can not be constructed),
            (2) err_message: an error message in case r is False.
            (3) A new formula (Form*) if possible, or None otherwise.

    Form2 formulas must be appear between parenthesis if it is a part of another formula,
    as in: ~(p v q) or in: p v (p^q). If it is the main formula, the parenthesis is not needed,
    as in: p v q

    Negation of Pred formulas also must be between parenthesis, as in
    '~', ('∀', 'x', '∃', 'y', 'p', ['x', 'y'])
    '''
    l = len(form)
    # print(f'form to represent: {form} - len: {l} - type: {type(form)}')
    if l == 0:
        err_message = 'Error: empty formula'
        return False, err_message, None
    elif (l == 1):
        return gen_repr1(form[0])
    elif (l == 2):
        return gen_repr2(form)
    elif (l > 2): # In case l > 2 : the main operator should be in ['^','v','->','<->']

        r, err_message, oper, opnd1,opnd2 = handle_precedence_of_operators(form)
        # print(f'rp: {r} - oper: {oper}  - opnd1: {opnd1} - opnd2:{opnd2}')
        if r : #This is a Form2 formula
            r, msg, new_form = gen_reprForm2(oper,opnd1,opnd2)
            # print(f'new_form: {new_form} - type:{type(new_form)}')
            return  r, msg, new_form
        else:
            return gen_reprFof(form)

    else:
        err_message = 'Wrong operator!'
        return r, err_message, None
# -----------------------------------------------------------------------------
def gen_repr1(form0):
    # print(f'form0: {form0}')
    if form0 in GlobalConstants.list_of_all_conecs:  # Those operations must have an operand - [ '~','^','v','->','<->']
        err_message = 'Error: an operand is missing.'
        return False, err_message, None
    elif form0  in [ '⊤','⊥']:  # Constants
        return True, '', Form0(form0)
    elif form0  in GlobalConstants.list_of_functs:  # Those operations must have an operand - ['p', 'q', 'r', 's', 't','u']
        return True, '', Form(form0)
    elif form0  in [ '⊤','⊥']:  # Constants
        return True, '', Form0(form0)
    else:
        err_message= 'Error: wrong formula.'
        return False, err_message, None

# -----------------------------------------------------------------------------
def gen_repr2(form):
    if form[0] == GlobalConstants.c_not:
        r, err_message, opnd1 = generate_represent(form[1])
        nf = Form1(GlobalConstants.c_not,opnd1)
        # print(f'nf: {nf}')
        return r, err_message, nf
    elif form[0] in GlobalConstants.list_of_cnecs :  # Those operations must have two operands - [ '^','v','->','<->']
        err_message = 'Error: the first operand is missing.'
        return False, err_message, None
    elif form[1] in GlobalConstants.list_of_cnecs:  # Those operations must have two operands - [ '^','v','->','<->']
        err_message = 'Error: the second operand is missing.'
        return False, err_message, None
    elif form[0] in GlobalConstants.list_of_functs:  # Those operations must have an operand - ['p', 'q', 'r', 's', 't', 'u']
        pred_vars = list(filter((',').__ne__, form[1]))  # remove all occurences of ',' from the list of vars
        nf = Pred(form[0],pred_vars)
        return True, '', nf
    else:
        err_message= 'Error: wrong formula.'
        # print(f'rp: {err_message} ')
        return False, err_message, None

#-----------------------------------------------------------------------------
def gen_reprForm2( oper, opnd1,opnd2):

    # print(f'oper: {oper}  - opnd1: {opnd1} - opnd2:{opnd2}')
    if oper == GlobalConstants.c_not:  # The main operation is the negation
        r, err_message, r_opnd1 = generate_represent(opnd1)
        return r, err_message, Form1(GlobalConstants.c_not, r_opnd1)
    elif type(opnd1) is Pred:
        r, error_message, r_opnd2 = generate_represent(opnd2)
        if r:
            return r, error_message, Form2(opnd1, oper, r_opnd2)
    else:
        r, error_message, r_opnd1 = generate_represent(opnd1)
        # print(f'r: {r}- error - {error_message}')
        if r:
            # print(f'opnd2:{opnd2}')
            r, error_message, r_opnd2 = generate_represent(opnd2)
            # print(f'r: {r} - r_opnd2: {r_opnd2}')
            if r:
                return r, error_message, Form2(r_opnd1, oper, r_opnd2)
            else:
                err_message = 'Error: the second operand is missing.'
                return r, err_message, None
        else:
            err_message= 'Error: the first operand is missing.'
            return r, err_message, None

# -----------------------------------------------------------------------------
def gen_reprFof(form):

    if form[0] in GlobalConstants.list_of_quants:  # ['∀', '∃']
        quant_list = []
        #Gets all quantifiers
        i = 0
        while form[i] in GlobalConstants.list_of_quants:  # ['∀', '∃']
            qt = Quant(form[i], form[i + 1])
            quant_list += [qt]
            i += 2
        if len(form) > i + 1:
            r, err_message, scope = generate_represent(form[i:])
        else:
            r, err_message, scope = generate_represent(form[i])

        if r:
            nf = Fof(quant_list, scope)
            return r, '', nf
        else:
            return r, err_message, scope

    err_message= 'Error: no quantifier found.'
    return False, err_message, None

# -----------------------------------------------------------------------------
# def is_predicate(form):
#     if (type(form) == tuple):
#         list_of_quants = form[0]
#         first_quant = list_of_quants[0][0]
#         if (first_quant == 'fa') or (first_quant == 'ex'):
#             return True
#     else:
#         return False


# -----------------------------------------------------------------------------

def handle_precedence_of_operators(form):
    """
        Handle precedence of operators, according to the sequence (~,v,^,->,<->).
        Traverses the string looking for the main operator. After this, looks
        for the left and right operands.

    :param form: a logic formula (string)
    :return: a logic formula : operand1 operator operand2
    """
    # print(f'form: {form} -  type : {type(form)}')
    first_occur = {}
    # O teste dos operandos deve vir aqui na ordem inversa da precedência
    if GlobalConstants.c_iff in form: # Gets position of the main operator
        first_occur[GlobalConstants.c_iff] = form.index(GlobalConstants.c_iff)
    if GlobalConstants.c_if in form:
        first_occur[GlobalConstants.c_if] = form.index(GlobalConstants.c_if)
    if GlobalConstants.c_and in form:
        first_occur[GlobalConstants.c_and] = form.index(GlobalConstants.c_and)
    if GlobalConstants.c_or in form:
        first_occur[GlobalConstants.c_or]= form.index(GlobalConstants.c_or)

    if len(first_occur) == 0:
        if form[0] == GlobalConstants.c_not:
            r = True
            err_message = ''  # No error message
            first_oper = GlobalConstants.c_not
            opnd1 = form[1:]
            opnd2 = form[1:]
            return r, err_message, first_oper, opnd1, opnd2
        else:
            first_oper = ''
            opnd1 = ''
            opnd2 = ''
            r = False
            err_message= 'Operand is missing!'
            return r, err_message, first_oper, opnd1, opnd2
    else:
        opers = list(first_occur)
        # print(f'opers: {opers}')

        first_oper = opers[0]
        position = first_occur[first_oper]

        # print(f'first_oper: {first_oper} at position: {position}')
        if position == 1: # First operand is a single variable
            opnd1 = form[0]
        else:
            opnd1 = form[:position]

        if len(form) - (position+1) == 1:  # Second operand is a single variable
            opnd2 = form[position + 1]
        else:
            opnd2 = form[position + 1:]

        r = True
        # err_message = 'Error handling precedence of operators.'
        err_message = ''

        return r, err_message, first_oper, opnd1, opnd2


# -----------------------------------------------------------------------------
# f = ['p', '->', 'p', 'v', 'q']
# r, err_message, first_oper, opnd1, opnd2 = handle_precedence_of_operators(f)
# print(f'r: {r}')
# print(f'err_message: {err_message}')
# print(f'first_oper: {first_oper}')
# print(f'opnd1: {opnd1}')
# print(f'opnd2: {opnd2}')

# qt1 = ('∀', 'x')
# qt2 = ('∃', 'y')
# l0 = ('∀', 'x', '∃', 'x', 'p', ['x','y'])
# ln0 = ('~',('∀', 'x', '∃',  'y', 'p', ['x','y']))
# l = ('∀', 'x', '∃',  'y', ('p', [ 'x', 'y'],'v','∀', 'z',  'q', ['z']))
# l1 =  ('p', '->', 'q')
# l2 =  ('p', 'v', 'q')
# l3 =  ('∀',  'x', '∃', 'y', 'u', [ 'x', 'y'])
# l4 =  ('~',('∀','x', 'u', ['x']))
# l5 =  ('∀','x', ( 'p',['x'], '^', 'q',['x']))
# l6 =  ('~',('∃', 'x', 'p', ['x']), '->',('∀', 'y', ('q',['y'], 'v', 's',  ['y'])))
# l7 =  ('∀', 'x', '∃',  'y', ('p', [ 'x', 'y'],'v','∀', 'z',  'q', ['z']))
#
# l6 = ['p', ['a']]
# l7 = ['p', ['a']]
#

# r, msg, form1 = generate_represent(p1)
# r, msg, form2 = generate_represent(p2)
# print(f'r: {r}')
# print(f'msg : {msg}')
# print(f'form1: {form1} - type: {type(form1)}')
# print(f'form2: {form2} - type: {type(form2)}')
# print(f'is?: {form1 == form2}')

# -----------------------------------------------------------------------------
def generate_list_represent(listOfForms):
    '''
        Generates a list of FORM* objects from a list o formulas

    :param listOfForms: a list of formulas (strings)
    :return r: a boolean, mes: an error message, formsRepr: a representarion
        for the formulas.
    '''
    
    formsRepr =[]  # Linhas de prova codificadas
    i = 0
    r = False
    while i < len(listOfForms):
        r, mes, form = generate_represent(listOfForms[i])
        if r:
            formsRepr.append(form)
            i+=1
        else:
            break
    return r, mes, formsRepr

# ---------------------------------------------------------------------------

# f=generate_represent((('~','p'),'^',( '~','q')))
# print(f)

# p1 = Form1('~', Form('p'))
# p2 = Form1('~', Form('p'))
#
# print(p1 == p2)

# form = ('p', '->', ('q', '->', 'r'))
# f= generate_represent(form)
# print(f)

# prem = '(p v s ^ (t <-> s)) -> q  & p & q'

# prem = 'fa           (X)ex(Y)p(X,         Y)   & p & fa(Z)ex(Z)q(X,Z)'
# prem = prem.replace('fa', ' fa ')  # Insert a space before and after 'fa'
# prem = prem.replace('ex', ' ex ')  # Insert a space before and after 'ex'
# prem = prem.replace(',', ' , ')  # Insert a space before and after ','
# prem = prem.replace('(', ' ( ')  # Insert a space before and after '('
# prem = prem.replace(')', ' ) ')  # Insert a space before and after ')'
# prem = prem.replace('->', ' -> ')  # Insert a space before and after '->'
# prem = prem.replace('<->', ' <-> ')  # Insert a space before and after '->'
# prem = prem.split()
# print(prem)

# ---------------------------------------------------------------------------
def isAtomic(form):
    if type(form) is Form: # p, q, r, ....
        return True
    elif type(form) is Form0: # T or ⊥
        return True
    elif type(form) is Form1: # ~ p
        if type(form.getOpnd1()) is Form: # ~p
            return True
        else: return False # ~~ p, ~( ), ...

# ---------------------------------------------------------------------------
def isInCNF(form):
    ''' A formula is in Conjunctive Normal Form if it is in this format:
        A1 ^ A2 ^ A3 ^ .... ^ An,
        where each Ai is in the format:
        B1 v B2 v  B3 v ... v Bm,
        where each Bj is a literal ( an atom ou a negated atom ).
       '''

    if isAtomic(form):
        return True
    elif type(form) is Form2: # type(form) is Form2
        oper = form.haveJustOneOper()
        if oper in [GlobalConstants.c_and, GlobalConstants.c_or]:
            return True
        elif form.getOper() is GlobalConstants.c_or:
            if isAtomic(form.getOpnd1()) and isAtomic(form.getOpnd2()):
                return True
            return False
        elif form.getOper() is GlobalConstants.c_and:
            if isInCNF(form.getOpnd1()) and isInCNF(form.getOpnd2()):
                return True
        else:
            False
    else:
        return False

# ---------------------------------------------------------------------------
def isInDNF(form):
    ''' A formula is in Disjunctive Normal Form if it is in this format:
        A1 v A2 v A3 v .... v An,
        where each Ai is in the format:
        B1 ^ B2 ^  B3 ^ ... ^  Bm,
        where each Bj is a literal ( an atom ou a negated atom ).
       '''
    if isAtomic(form):
        return True
    elif type(form) is Form2: # type(form) is Form2
        oper = form.haveJustOneOper()
        if oper in [GlobalConstants.c_and, GlobalConstants.c_or]:
            return True
        elif form.getOper() is GlobalConstants.c_or:
            if isAtomic(form.getOpnd1()) and isAtomic(form.getOpnd2()):
                return True
            return False
        elif form.getOper() is GlobalConstants.c_and:
            if isInDNF(form.getOpnd1()) and isInDNF(form.getOpnd2()):
                return True
        else:
            return False
    else:
        return False
# -----------------------------------------------------------------------------

#
# f01 = Form('p')
# f03 = Form('q')
# f04 = Form('r')
#
# f11 = Form1('~',f01)
# f13 = Form1('~',f11)
# #
# f21 = Form2(f01,GlobalConstants.c_or,f03)
# f22 = Form2(f21,GlobalConstants.c_and,f21)
# f23 = Form2(f22,GlobalConstants.c_and,f21)
#
# f31 = Form2(f01,GlobalConstants.c_and,f03)
# f32 = Form2(f21,GlobalConstants.c_or,f22)
# f33 = Form2(f32,GlobalConstants.c_or,f21)
# f34 = Form2(f33,GlobalConstants.c_or,f21)
#
# form = f34
# r = isInCNF(form)
# if r:
#     print(f'{form} is in CNF')
# else:
#     print(f'{form} is not in CNF')
#
# print(f'oper: {form.haveJustOneOper()}')