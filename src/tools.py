"""
Created on Tue Nov 07 08:19: 2023

@author: cedric
"""

import copy
import os
from itertools import chain, combinations

import forms as fms
import infRules as inf
import equivRules as equiv
import predRules as pred
import deducInfer as ddi


# -----------------------------------------------------------------------------
class Prover():
    """
    This class implements the prover
    """

    def __init__(self, **kwargs):
        super().__init__(**kwargs)


        # self.time = NumericProperty(0)  # Contador de tempo
        self.counter = 0
        self.errors = 0

        self.rti = inf.createInfRules()

        self.rte = equiv.createEquRules()
        self.rtp = pred.createPredRules()
        self.rule_table = (self.rti, self.rte, self.rtp)

        self.infCkb_ref = {}
        self.equivCkb_ref = {}
        self.predInfCkb_ref = {}
        self.predEquivCkb_ref = {}
        self.proofCkb_ref = {}

        self.argument_conclusion = ''
        self.argument_premisses = []

        # self.premisses = []
        # self.conclusion = []
        self.line_index = 0
        self.proof_lines = []
        self.ex_particularizations = []  # List of proof lines where existential particularization where applied
        # self.selected_proof_lines = []
        # When an inference rule is selected,
        # if index is [0,1,2], type must be 'HYP', otherwise must be 'INF'
        # selected_rule_index = (rule_type, rule_index)
        # self.selected_rule_index = None # (rule_type, rule_index)

        self.list_of_hypothesis = []
        # self.begin_hypothesis = -1
        self.forbidden_lines = []
        self.list_of_problems = []

        self.only_equiv_rules = False

        # for predicate calculus
        # --------------------------------------------------------
        # previous_used_constant_list = [] # List of vars used in a demonstration
        # bound_variables = [] # List of vars bound to quantifiers
        # previous_free_vars = [] # List of free variables occurring premiss or hypothesis
        # constants_in_free_premisses = []  # List of constants occurring in an open premiss or hypothesis
        # deducted_from_ex_part = []  # List of vars used in existential particularization
        # --------------------------------------------------------

        self.selected_rule_index = None
        self.selected_rule_type = None
        self.selected_new_term = None
        self.selected_quantifier = None
        self.student = ("00000", "cedric")
        self.file = ("", "", "")

    # -----------------------------------------------------------------------------
    def resetApp(self):
        self.time = 0
        self.errors = 0
        self.backs = 0
        self.tProof = 0  # Begin of proving process
        self.line_stack = []
        self.lineIndex = 0
        self.argument_conclusion = ''
        self.argument_premisses = []
        # self.premisses = []
        # self.conclusion = ''
        self.proof_lines = []  # Proof lines - initially keeps the argument premisses
        self.ex_particularizations = []  # List of proof lines where existential particularization where applied
        self.selected_rule_index = None
        self.list_of_hypothesis = []
        self.forbidden_lines = []
        self.only_equiv_rules = False

        # self.previous_used_constant_list = [] # Constants used em demonstration (by applying particularization)
        # self.bound_variables = []
        # self.previous_free_vars = []
        # self.deducted_from_ex_part = []

        # self.stopClock()

        return

    # -----------------------------------------------------------------------------
    def input_an_argument(self, selected_problem):
        '''

        '''
        lp = selected_problem.split(' - ')  # lp = [index, argument]
        # print(f'lp: {lp}')

        try:
            input_list = lp[1].replace('|-', fms.GlobalConstants.c_ass)  # Replace '->' by  '⊢'
            l_terms = input_list.split(' ' + fms.GlobalConstants.c_ass + ' ')  # Conclusion must appear after ' ⊢ "
            # l_terms is a list of 2 elements: a string of premisses and a conclusion
            s_premisses = str(l_terms[0])
            s_conclusion = l_terms[1]
        except:
            error_message0 = selected_problem
            error_message = error_message0 + '\nArgument malformed. Please, fix it.'
            return False, error_message

        # print(f's_premisses: {s_premisses}')
        l_premisses = s_premisses.split(' , ')  # Premisses must be separated by  SPACE-COMMA-SPACE
        # print(f'l_premisses: {l_premisses}')

        r, msg = self.prepare_list_of_premisses(l_premisses)
        if not r:
            return r, msg
        else:
            r, msg = self.prepare_conclusion(s_conclusion)
            if not r:
                return r, msg
            else:
                return True, ''

    # -----------------------------------------------------------------------------
    def prepare_list_of_premisses(self, l_premisses):

        tools = UsefullTools()

        # Preparing the list of premisses
        for prem in l_premisses:
            # print(f'prem antes: {prem}')
            prem = tools.insert_spaces(prem)
            # print(f'prem depois: {prem}')
            list_prem = prem.split()
            # Variables in predicates must be separated by COMMAS WITHOUT spaces between it
            list_prem = list(filter((',').__ne__, list_prem))  # remove all occurrences of ',' from the input_string
            # print(f'list_prem: {list_prem}')
            r, msg = self.input_premiss(list_prem)  # Include a new premiss
            if not r:
                return r, msg
        return True, ''

    # -----------------------------------------------------------------------------
    def prepare_conclusion(self, s_conclusion):

        # print(f's_conclusion0: {s_conclusion}')
        # Preparing the conclusion
        tools = UsefullTools()
        s_conclusion = tools.insert_spaces(s_conclusion)
        # print(f's_conclusion1: <{s_conclusion}> - type: {type(s_conclusion)}')
        list_s_conclusion = s_conclusion.split()
        list_s_conclusion = list(
            filter((',').__ne__, list_s_conclusion))  # remove all occurrences of ',' from the input_string

        if list_s_conclusion[0] == fms.GlobalConstants.cnf:
            # self.ids.in_arg_label.text = self.ids.in_arg_label.text + '\n' + \
            #                              fms.GlobalConstants.c_equiv + ' CNF'
            self.argument_conclusion = fms.GlobalConstants.cnf
            self.only_equiv_rules = True
            # self.ids.in_arg.ids.in_prem_or_concl.text = 'Input a Premiss or Conclusion'
            return True, ''
        elif list_s_conclusion[0] == fms.GlobalConstants.dnf:
            # self.ids.in_arg_label.text = self.ids.in_arg_label.text + '\n' + \
            #                              fms.GlobalConstants.c_equiv + ' DNF'
            self.argument_conclusion = fms.GlobalConstants.dnf
            self.only_equiv_rules = True
            return True, ''
        elif list_s_conclusion[0] == fms.GlobalConstants.true:
            # self.ids.in_arg_label.text = self.ids.in_arg_label.text + '\n' + \
            #                              fms.GlobalConstants.c_equiv + ' ' + fms.GlobalConstants.true
            self.argument_premisses = fms.Form0(fms.GlobalConstants.true)
            self.only_equiv_rules = True
            return True, ''
        elif list_s_conclusion[0] == fms.GlobalConstants.false:
            # self.ids.in_arg_label.text = self.ids.in_arg_label.text + '\n' + \
            #                              fms.GlobalConstants.c_equiv + ' ' + fms.GlobalConstants.false
            self.argument_conclusion = fms.Form0(fms.GlobalConstants.false)
            self.only_equiv_rules = True
            return True, ''
        else:
            r, msg = self.input_conclusion(list_s_conclusion)  # Include conclusion
            if not r:
                return False, msg
            else:
                return True, ''

    # -----------------------------------------------------------------------------
    def input_premiss(self, formula):  # formula is in string format
        '''
            Input a new premiss.
            The parameter form is just to check if the text ( a string ) in the input screen
            has been changed.
            The input to be processed into a new premiss is stored in the 'self.ids.in_arg_label.text'
            property.
        '''
        # print('INPUTTING PREMISS')
        # print(f'formula : {formula} - type: {type(formula)}')

        if self.argument_conclusion != '':  # Conclusion already entered.
            error_message = 'Argument already entered.\nGo to PROOF window, please.'
            return False, error_message
        else:
            tools = UsefullTools()
            r1, error_message, new_formula = tools.remove_parenthesis(formula)
            if not r1:
                return r1, error_message
            else:
                # print(f'new_formula: {new_formula}')
                r2, error_message, prep_formula = fms.generate_represent(new_formula)
                if not r2:
                    return r2, error_message
                else:
                    # print(f'r2: {r2} - prep_formula: {prep_formula}  - type: {type(prep_formula)}')
                    self.argument_premisses.append((prep_formula, 'P'))
                    # print(f'argument_premisses: {self.argument_premisses}')

                    self.proof_lines = self.argument_premisses
                    self.argument_premisses = self.argument_premisses.copy()  # Just a copy of input premisses

                    self.line_index = len(self.proof_lines)  # Updates line proof numbering
                    return True, ''

    # -----------------------------------------------------------------------------
    def input_conclusion(self, formula):

        # print('INPUTING CONCLUSION')
        # print(f'formula : {formula} - type: {type(formula)}')

        if self.argument_conclusion != '':  # Conclusion already entered.
            error_message = 'Argument already entered.\nGo to PROOF WINDOW, please.'
            return False, error_message
        elif self.argument_premisses == []:
            error_message = 'Enter a premiss first, please.'
            return False, error_message
        else:
            if formula == []:  # An empty conclusion
                error_message = 'Enter a conclusion first, please.'
                return False, error_message
            else:
                tools = UsefullTools()
                r, error_message, prep_formula = tools.remove_parenthesis(formula)
                if not r:
                    return False, error_message
                else:
                    r, error_message, rep_formula = fms.generate_represent(prep_formula)
                    if not r:
                        return False, error_message
                    else:
                        # self.ids.in_arg_label.text = self.ids.in_arg_label.text + '\n' + \
                        #                              fms.GlobalConstants.c_ass + ' ' + str(formula)
                        self.argument_conclusion = rep_formula
                        # self.ids.in_arg.ids.in_prem_or_concl.text = 'Input a Premiss or Conclusion'
                        # print(f'self.argument_conclusion: {self.argument_conclusion}')

                        self.conclusion = self.argument_conclusion
                        return True, ''

    # -----------------------------------------------------------------------------
    def prove(self, rule_type, sel_rule, selected_proof_line_indexes, proof_lines_list, user_response):
        '''

        user_response: (user_input: number of times to input, user_resp)
        '''
        tools = UsefullTools()

        r, msg = tools.check_if_the_lines_are_forbidden(selected_proof_line_indexes, self.forbidden_lines)

        if not r:  # User selected more than one line or the line selected is forbidden
            return r, msg, 0,  None, proof_lines_list
        else:
            # print(rule_type, sel_rule, selected_proof_line_indexes)
            proof_lines = []
            for l in proof_lines_list:
                proof_lines.append(l)

            if sel_rule is None:  # No rules were selected
                error_message = 'Choose a rule first, please.'
                user_input = 0
                return False, error_message, user_input, None, None
            if not selected_proof_line_indexes:  # No proof lines where selected - selected_proof_line_indexes = []
                error_message = 'Choose at least one proof line first, please'
                user_input = 0
                return False, error_message, user_input, None, None
            # CHECK THIS IN CASE OF PROVING A THEOREM
            if not proof_lines:  # There are no proof lines - self.proof_lines = []
                error_message = 'Enter premisses first, please.'
                user_input = 0
                return False, error_message, user_input, None, None

            r, msg, user_input, new_line, proof_line_updated = \
                self.apply_rule(rule_type, sel_rule,
                                selected_proof_line_indexes,
                                proof_lines, user_response)

            self.proof_lines = proof_line_updated
            return r, msg, user_input, new_line, proof_line_updated

    # -----------------------------------------------------------------------------

    def apply_rule(self, rule_type, rule_number, selected_proof_line_indexes, proof_line_list, user_response):
        '''
        Apply a selected rule to a set of selected proof lines.
        '''

        # tools = UsefullTools()
        # print(f'proof_line_list: {proof_line_list}')

        if rule_type == 'HYP':  # Hypothesis rule
            rule = self.rti[rule_number]  # Selected rule
            error_message = "Wrong number of selected proof_lines."
            if len(selected_proof_line_indexes) != len(rule.getPremis()):
                return False, error_message, 0, None, proof_line_list
            else:
                r, msg, user_input, new_line = \
                    self.apply_hypothesis_rule(rule_number, proof_line_list, user_response)
        elif rule_type == 'INF':  # Inference rule
            rule = self.rti[rule_number]  # Selected rule
            error_message = "Wrong number of selected proof_lines."
            if len(selected_proof_line_indexes) != len(rule.getPremis()):
                return False, error_message, 0, None, proof_line_list
            else:
                r, msg, user_input, new_line = \
                    self.apply_inference_rule(rule, selected_proof_line_indexes,
                                              proof_line_list, user_response)
        elif (rule_type == 'EQ') or (rule_type == 'PRED_E'):
            if rule_type == 'EQ':
                rule = self.rte[rule_number]
            else:
                rule = self.rtp[1][rule_number]

            error_message = "Wrong number of selected proof_lines."
            if len(selected_proof_line_indexes) != 1:
                return False, error_message, 0, None, proof_line_list
            else:
                r, msg, user_input, new_line = (
                    self.apply_eq_or_pred_eq_rule(rule_type, rule_number,
                                                  selected_proof_line_indexes,
                                                  proof_line_list, user_response))

        # elif rule_type == 'EQ':  # Equivalence rule
        #     rule = self.rte[rule_number]  # Selected rule
        #     error_message = "Wrong number of selected proof_lines."
        #     if len(selected_proof_line_indexes) != 1:
        #         return False, error_message, 0, None, proof_line_list
        #     else:
        #         r, msg, user_input, new_line = \
        #             self.apply_equivalence_rule(rule,
        #                                         selected_proof_line_indexes,
        #                                         proof_line_list, user_response)
        #
        # elif rule_type == 'PRED_E':  # Predicate equivalence rule
        #     rule = self.rtp[1][rule_number]
        #     user_input = 0
        #     error_message = "Wrong number of selected proof_lines."
        #     if len(selected_proof_line_indexes) != 1:
        #         return False, error_message, user_input, None, proof_line_list
        #     else:
        #         r, msg, user_input, new_line = \
        #             self.apply_predicate_equivalence_rule(rule,
        #                                                   selected_proof_line_indexes,
        #                                                   proof_line_list)
        else:  # rule_type == 'PRED_I' - Predicate inference rule
            rule = self.rtp[0][rule_number]
            error_message = "Wrong number of selected proof_lines."
            if len(selected_proof_line_indexes) != 1:
                return False, error_message, 0, None, proof_line_list
            else:
                r, msg, user_input, new_line = \
                    self.apply_predicate_inference_rule(rule,
                                                        selected_proof_line_indexes,
                                                        proof_line_list,
                                                        user_response)

        if r and not user_input:
            rule_nick = rule.getNick()
            self.line_index += 1  # Increments proof line numeration
            # Inserts new line in proof lines list
            lines_used = str(rule_nick)+"-"+str(selected_proof_line_indexes)
            proof_line_list.append((new_line, lines_used ))
            # content = ' '.join(new_line)
            # lines_used = ' , '.join(map(str,selected_proof_line_indexes))
            # new_line = {"content": content, "rule_used": rule_nick, "lines_used":lines_used, "type:":"add"}
            # print(f"new_line: {new_line}")
            # print(f"new_line: {new_line}")

        # print(f"r= {r}")
        return r, msg, user_input, new_line, proof_line_list

    # -----------------------------------------------------------------------------

    def apply_hypothesis_rule(self, rule_number, proof_line_list, user_response):

        # print('PROVING HYPOTHESIS:')
        # To introduce a hypothesis and to remove it there is no need
        # to select a line

        rule = self.rti[rule_number]  # Selected rule
        rule_nick = rule.getNick()
        # print(f'rule_nick: {rule_nick}')

        if rule_nick == 'ADHYP':  # Remove a hypothesis inference rule
            r, msg, user_input, new_line = self.add_temp_hypothesis(proof_line_list, user_response)
            return r, msg, user_input, new_line
        elif rule_nick == 'RMHYP':  # Remove a hypothesis inference rule
            r, msg, new_line = self.remove_temp_hypothesis(proof_line_list)
            user_input = 0
            return r, msg, user_input, new_line
        elif rule_nick == 'ABsd':  # Replace the hypothesis by its negation
            r, msg, new_line = self.remove_temp_hypothesis_absurd(proof_line_list)
            user_input = 0
            return r, msg, user_input, new_line
        else:
            user_input = 0
            error_message = 'Wrong rule selected.'
            return False, error_message, user_input, ''

    # -----------------------------------------------------------------------------
    def add_temp_hypothesis(self, proof_line_list, user_response):

        user_input, new_hypothesis, _ = user_response
        # print(f'user_resp: {new_hypothesis}')
        if new_hypothesis is None:
            user_input = 1
            return True, '', user_input, new_hypothesis
        else:
            user_input = 0
            index = len(proof_line_list) - 1
            self.list_of_hypothesis.append(index + 1)  # Includes the new hypothesis in the list o hypothesis
            return True, '', user_input, new_hypothesis

    # -----------------------------------------------------------------------------
    def remove_temp_hypothesis(self, proof_line_list):

        # The last proof line is considered the consequent of the
        # conditional derived from the last introduced hypothesis
        if len(self.list_of_hypothesis) != 0:
            begin_hypothesis = self.list_of_hypothesis[-1]
            ant = proof_line_list[begin_hypothesis]
            conseq = proof_line_list[-1]  # Last proof line
            antecedent = self.remove_rule_reference(ant)
            consequent = self.remove_rule_reference(conseq)
            new_line = fms.Form2(antecedent, fms.GlobalConstants.c_if, consequent)
            i = begin_hypothesis
            while i < len(proof_line_list):
                self.forbidden_lines.append(i)
                i += 1
            print(f'self.forbidden_lines: {self.forbidden_lines}')
            self.list_of_hypothesis.pop()  # Excludes hypothesis
            return True, '', new_line
        else:
            error_message = 'No hypothesis were introduced so far.' \
                            '\n The rule <Remove Hypothesis> cannot be applied.' \
                            '\nPlease, try again.'
            return False, error_message, ''

    # -----------------------------------------------------------------------------
    def remove_temp_hypothesis_absurd(self, proof_line_list):

        # The last proof line is a contradiction
        # so, the negation of the hypothesis can be added to the proof lines
        if len(self.list_of_hypothesis) != 0:
            begin_hypothesis = self.list_of_hypothesis[-1]
            ant = proof_line_list[begin_hypothesis]
            conseq = proof_line_list[-1]  # Last proof line
            antecedent = self.remove_rule_reference(ant)
            consequent = self.remove_rule_reference(conseq)
            # print(f' antecedent: {antecedent} - type: {type(antecedent)}')
            # print(f' consequent: {consequent} - type: {type(consequent)}')
            # print(f' opnd1: {consequent.getOpnd1()} - type: {type(consequent.getOpnd1())}')
            if consequent.getOpnd1() == fms.GlobalConstants.false:
                new_line = fms.Form1(fms.GlobalConstants.c_not, antecedent)
                # print(f' new_line: {new_line}')
                i = begin_hypothesis
                while i < len(self.proof_lines):
                    self.forbidden_lines.append(i)
                    i += 1
                self.list_of_hypothesis.pop()  # Excludes hypothesis
                return True, '', new_line
            else:
                error_message = 'This formula is not a contradiction.' \
                                '\n The rule <Remove Hypothesis by Absurd> cannot be applied.' \
                                '\nPlease, try again.'
                return False, error_message, ''
        else:
            error_message = 'No hypothesis were introduced so far.' \
                            '\n The rule <Remove Hypothesis by Absurd> cannot be applied.' \
                            '\nPlease, try again.'
            return False, error_message, ''

    # -----------------------------------------------------------------------------
    def apply_inference_rule(self, rule, selected_proof_line_indexes, proof_line_list, user_response):
        '''
        Apply an inference rule to a set of selected proof lines.
        :param rule: the selected rule
        :param selected_proof_line_indexes: a list to the selected proof lines
        :param proof_line_list: the list of proof lines
        :return: True/False, an error message and the new proof line generated
        '''


        # print('PROVING INFERENCE:')

        # Put all selected proof lines into a list
        sel_proof_lines = []
        for i in selected_proof_line_indexes:
            # print(f"i: {i}")
            # print(f"proof_line_list: {proof_line_list}")
            sel_proof_lines.append(proof_line_list[i])

        if (self.argument_conclusion == fms.GlobalConstants.cnf or self.argument_conclusion == fms.GlobalConstants.dnf \
                or self.argument_conclusion == fms.GlobalConstants.true or self.argument_conclusion == fms.GlobalConstants.false):
            error_message = 'Only equivalence rules \n can be used \n\n when proving equivalences.'
            user_input = 0
            return False, error_message, user_input, None
        else:
            user_resp, new_disjunct, _ = user_response
            s_proof_lines = self.remove_rule_references(sel_proof_lines)
            # print(f'proof_lines: {s_proof_lines}')
            rule_nick = rule.getNick()
            if rule_nick == 'ADD1':  # Rule 'Adição_1: p=> p v q'
                if new_disjunct is None:
                    user_input = 1
                    return True, '', user_input, new_disjunct
                else:
                    user_input = 0
                    new_line = fms.Form2(s_proof_lines[0], fms.GlobalConstants.c_or, new_disjunct)
                    return True, '', user_input, new_line

                # r, msg, prep_disjunct = self.prepare_disjunct(s_proof_lines)
                # if not r:
                #     return r, msg, prep_disjunct
                # else:
                #     new_line = fms.Form2(s_proof_lines[0], fms.GlobalConstants.c_or, prep_disjunct)
                #     return r, msg, new_line
            elif rule_nick == 'ADD2':  # Rule 'Adição_2: p=> q v p'
                if new_disjunct is None:
                    user_input = 1
                    return True, '', user_input, new_disjunct
                else:
                    user_input = 0
                    new_line = fms.Form2(new_disjunct, fms.GlobalConstants.c_or, s_proof_lines[0])
                    return True, '', user_input, new_line

                # r, msg, prep_disjunct = self.prepare_disjunct(s_proof_lines)
                # if not r:
                #     return r, msg, prep_disjunct
                # else:
                #     new_line = fms.Form2(prep_disjunct, fms.GlobalConstants.c_or, s_proof_lines[0])
            else:
                proof_lines = self.remove_rule_references(sel_proof_lines)
                # print(f'proof_lines: {proof_lines}')
                r, msg, new_line = ddi.apply_inference_rule(rule,
                                                            proof_lines)  # Apply the selected rule to de selected lines
        user_input = 0
        return r, msg, user_input, new_line

    # -----------------------------------------------------------------------------
    def remove_rule_references(self, proof_lines):
        '''
        :param proof_lines: (proof line, rule used (or premiss - 'P'))
        :return: a list of proof lines, without reference to rules used
        '''

        pf = []
        for line in proof_lines:
            l = self.remove_rule_reference(line)
            pf.append(l)
        return pf

    # -----------------------------------------------------------------------------
    def remove_rule_reference(self, proof_line):
        '''
        :param proof_line: (proof line, rule used (or premiss - 'P'))
        :return: the proof line, without reference to rules used
        '''

        l, r = proof_line

        return l

    # -----------------------------------------------------------------------------
    def apply_eq_or_pred_eq_rule(self, rule_type, rule_number, selected_proof_line_indexes, proof_line_list, user_response):
        '''
               Apply an equivalence rule to a selected proof line. Just one proof line
               must be selected
               :param rule: the selected rule
               :param selected_proof_line_indexes: list of the indices of the selected proof lines
               :param proof_line_list: the list of proof lines
               :return: True/False, an error message
               '''
        # print('PROVING EQUIVALENCES:')

        tools = UsefullTools()

        user_resp, sub_formula, total_ou_partial = user_response

        selected_proof_line = proof_line_list[selected_proof_line_indexes[0]]
        sel_lines = self.remove_rule_references([selected_proof_line])
        # print(f'sel_lines: {sel_lines}')
        line = sel_lines[0]  # Just one line was selected
        # print(f'line: {line} - type: {type(line)}')
        ind_form_list = fms.index_form(0, line)
        options = tools.get_options(ind_form_list)
        print(f'options::::: {options}')

        if (sub_formula is None):
                # and (total_ou_partial == "partial"):
            user_input = 1
            return True, '', user_input, (["Select a part of the formula, please."], [options])
        else:
            original_form = options[0]
            r, msg, user_input, new_line = self.apply_equivalence_rule_Nova(rule_type, rule_number,original_form, line, user_response)
            return r, msg, user_input, new_line


            # if rule_type == 'EQ':
            #     rule = self.rte[rule_number]  # Selected rule
            #     r, msg, user_input, new_line = \
            #         self.apply_equivalence_rule(rule,options,form,user_response)
            #
            #     return r, msg, user_input, new_line
            #     # if sub_formula == options[0]:  # The rule is applied to the whole formula
            #     #     r, msg, new_line = self.apply_equiv_rule(rule, form)
            #     #     user_input = 0
            #     #     return r, msg, user_input, new_line
            #     # else:
            #     #     original_form = options[0]  # The first option is the whole formula
            #     #     r, msg, new_line = self.apply_equiv_in_part_or_the_line(rule,
            #     #                                                             original_form,
            #     #                                                             sub_formula)
            #     #     user_input = 0
            #     #     return r, msg, user_input, new_line
            # else:
            #     rule = self.rtp[1][rule_number]
            #     pass
    # -----------------------------------------------------------------------------
    def apply_equivalence_rule_Nova(self, rule_type, rule_number, original_form, line, user_response):
        '''
        Apply an equivalence rule to a selected proof line. Just one proof line
        must be selected
        :param rule: the selected rule
        :param selected_proof_line_indexes: list of the indices of the selected proof lines
        :param proof_line_list: the list of proof lines
        :return: True/False, an error message
        '''

        user_resp, sub_formula, total_or_partial = user_response

        if total_or_partial  == "total":
            if rule_type == 'EQ':
                rule = self.rte[rule_number]

                r, msg, new_line = self.apply_equiv_rule(rule, line)
            else:
                rule = self.rtp[1][rule_number]
                r, msg, new_line = self.apply_predicate_equivalence_rule2(rule, line)

            user_input = 0
            return r, msg, user_input, new_line
        else:
            r, msg, new_line = self.apply_partial(rule_type, rule_number,original_form,sub_formula)
            user_input = 0
            return r, msg, user_input, new_line

    # elif rule_type == 'PRED_E':  # Predicate equivalence rule

    #     rule = self.rtp[1][rule_number]
    #     user_input = 0
    #     error_message = "Wrong number of selected proof_lines."
    #     if len(selected_proof_line_indexes) != 1:
    #         return False, error_message, user_input, None, proof_line_list
    #     else:
    #         r, msg, user_input, new_line = \
    #             self.apply_predicate_equivalence_rule(rule,
    #                                                   selected_proof_line_indexes,
    #                                                   proof_line_list)



    # -----------------------------------------------------------------------------
    def apply_equiv_rule(self, rule, form):
        '''
        Apply the selected rule to the WHOLE proof line selected
        :param rule: the selected rule
        :param form: the form (the selected proof line)
        :return: True/False, an error message and the new proof line generated
        '''

        if type(form) is fms.Fof:
            scope = form.getScope()
            quants = form.getQuantifiers()
            r, msg, n_scope = equiv.applyEquivRule(rule, [scope])
            new_line = fms.Fof(quants, n_scope)
        else:
            r, msg, new_line = equiv.applyEquivRule(rule, [form])

        return r, msg, new_line

    # -----------------------------------------------------------------------------
    def apply_partial(self, rule_type, rule_number, original_form, selection):
        '''
        Apply the selected rule to a part of the proof line selected
        :param rule: the selected rule
        :param original_form: the original proof line selected
        :param selection: the sub_formula of the original proof line
        :return: True/False, an error message and the new proof line generated
            the result of application of the rule to a part of the line
            must replace the original part of the line
        '''

        original_form = original_form.split(' - AT POS ')[0]
        sform_original, form_list, begin, end = self.get_partial_formula(selection)

        tools = UsefullTools()
        r, error_message, prep_formula = tools.remove_parenthesis(form_list)
        if not r:
            return r, error_message, None
        else:
            # print(f'prep_formula: {prep_formula}')
            r, error_message, rep_formula = fms.generate_represent(prep_formula)
            # print(f'rep_formula: {rep_formula} - type: {type(rep_formula)}')
            if not r:
                return r, error_message, None
            else:
                if rule_type == "EQ":
                    rule = self.rte[rule_number]
                    r, error_message, new_form = equiv.applyEquivRule(rule, [rep_formula])
                    # print(f'newForm: {new_form} - type: {type(new_form)}')
                else:
                    rule = self.rtp[1][rule_number] # Equivalence predicate rule
                    r, msg, new_form = self.apply_predicate_equivalence_rule2( rule,rep_formula)

                if not r:
                    return r, error_message, None
                else:
                    s_newForm = str(new_form)

                    if len(s_newForm) > 2:
                        if original_form[begin - 1] == '(' and original_form[end + 1] == ')':
                            pass
                        else:
                            s_newForm = "(" + s_newForm + ")"

                    cnt = fms.GlobalConstants()
                    # print(f'snewForm: {s_newForm} - type: {type(s_newForm)}')
                    s_newForm = s_newForm.replace(cnt.c_not + cnt.c_not, cnt.c_not + ' ' + cnt.c_not)
                    # print(f's_newForm2: {s_newForm} - type: {type(s_newForm)}')

                    # print(f'original_form: {original_form} - type: {type(original_form)}')
                    # print(f'sform_original: {sform_original} - len(sform_original): {len(sform_original)}')
                    new_text = original_form.replace(sform_original, s_newForm)
                    # print(f'new_text: {new_text}')
                    r, msg, prep_new_text = tools.prepare_new_formula(new_text)
                    # print(f'prep_new_text: {prep_new_text}')
                    return r, msg, prep_new_text

    # -----------------------------------------------------------------------------
    def get_partial_formula(self, selection):

        # print(f'\n\nselection: {selection}, type :{type(selection)}')

        # s_original_form = original_form.split(' - AT POS ')[0]

        l_selection = selection.split(' - AT POS ')
        # print(f'l_selection: {l_selection}')

        sform = l_selection[0]
        sform_original = copy.copy(sform)

        # print(f'sform_original: {sform_original} - type: {type(sform_original)}')
        initial_position = l_selection[1]
        # print(f'\n\ninitial_position: {initial_position}')
        # print(f'sform: {sform} - len(sform): {len(sform)}')

        begin = int(initial_position)
        end = int(initial_position) + len(sform) - 1

        # print(f'begin: {begin}')
        # print(f'end: {end}')

        tools = UsefullTools()
        sform = tools.insert_spaces(sform)
        # print(f'sform: {sform}')

        l_sform = sform.split()  # Transform into a list without spaces
        l_sform = list(filter((',').__ne__, l_sform))  # remove all occurrences of ',' from the input_string
        # print(f'l_sform: {l_sform}')

        return sform_original, l_sform, begin, end

    # -----------------------------------------------------------------------------
    def prepare_disjunct(self, selected_proof_lines):

        tools = UsefullTools()
        r, msg = tools.check_if_just_one_line_selected(selected_proof_lines)

        if not r:
            return r, msg, None
        else:
            r, msg, new_disjunct = tools.input_formula()

            return r, msg, new_disjunct


    # -----------------------------------------------------------------------------
    def apply_predicate_inference_rule(self, rule, selected_proof_line_indexes,
                                       proof_line_list, user_response):
        """

        """

        # print('PROVING INFERENCE IN PREDICATES:')
        # print(f'user response: {user_response}')
        user_input, user_resp, _ = user_response

        # To user predicates rules, just one line must be selected
        rule_nick = rule.getNick()
        # print(f'rule_nick: {rule_nick}')

        line_number = selected_proof_line_indexes[0]  # Just one proof line can be selected
        # print(f'proof_line_list: {proof_line_list}')

        selected_line = proof_line_list[line_number]
        # print(f'selected_line: {selected_line} - type: {type(selected_line)}')
        form = self.remove_rule_reference(selected_line)
        # print(f'form: {form} - type: {type(form)}')

        if (rule_nick == 'PU_lr') or (rule_nick == 'PE_lr'):
            if type(form) is not fms.Fof:
                error_message = 'The rule <' + rule.name + \
                                '>\ncannot be applied to this formula.' + '\nPlease, try again.'

                return False, error_message, user_input, None
            else:
                r, msg, quant_options = self.get_quantifier_options(form, line_number, rule_nick)
                # print(f'quant_options: {quant_options}')
                term_options = fms.GlobalConstants.list_of_terms
                # print(f'term_options: {term_options}')

                if user_resp is None:
                    user_input = 1  # User must select a quantifier and a term
                    return True, msg, user_input, \
                        (["Select a term, please.","Select a quantifier, please.", ],
                         [term_options,quant_options,])
                else:
                    selected_quant = user_resp[0]
                    selected_term = user_resp[1]
                    # print(f'selected_quant: {selected_quant}')
                    # print(f'selected_term: {selected_term}')
                    r, msg, new_line = self.apply_particularization_rule(form, line_number, selected_quant,
                                                                         selected_term, proof_line_list,
                                                                         self.forbidden_lines)
                    user_input = 0
                    return r, msg, user_input, new_line
        elif rule_nick == 'GU_lr':

            var_options = fms.GlobalConstants.list_of_vars
            # print(f'var_options: {var_options}')
            tools = UsefullTools()
            term_options = tools.get_scope_terms(form, [])
            term_options =  list(set(term_options)) # Remove repeated elements
            # term_options = fms.GlobalConstants.list_of_terms
            # print(f'term_options: {term_options}')
            if user_resp is None:
                user_input = 1  # User must select a var and a term
                return True, ' ', user_input,\
                    ([ "Select a term, please.","Select a variable, please."], [term_options,var_options])
            else:
                selected_var = user_resp[0]
                selected_term = user_resp[1]
                # print(f'selected_var: {selected_var}')
                # print(f'selected_term: {selected_term}')
                r, msg, new_line = self.apply_univ_generalization_rule(form,
                                                                       proof_line_list,
                                                                       selected_var, selected_term)
                return r, msg, user_input, new_line
        elif rule_nick == 'GE_lr':
            var_options = fms.GlobalConstants.list_of_vars
            # print(f'var_options: {var_options}')
            tools = UsefullTools()
            term_options = tools.get_scope_terms(form, [])
            term_options =  list(set(term_options)) # Remove repeated elements
            # term_options = fms.GlobalConstants.list_of_terms
            # print(f'term_options: {term_options}')
            if user_resp is None:
                user_input = 1  # User must select a var and a term
                return True, ' ', user_input, \
                    (["Select a term, please.","Select a variable, please."],
                     [ term_options,var_options])
            else:
                r, msg, user_input, new_line = self.apply_exist_generalization_rule(user_response, form)

                return r, msg, user_input, new_line
        else:
            error_message = 'Wrong rule selected.'
            return False, error_message, user_input, None


    # -----------------------------------------------------------------------------
    def get_quantifier_options(self, form, line, rule_nick):

        # print(f'form: {form}')
        # print(f'line: {line}')
        # print(f'rule_nick: {rule_nick}')

        quantifier_list = form.getQuantifiers()
        # print(f'quant_list: {quantifier_list}')
        quant_options = []
        if rule_nick == 'PU_lr':
            for q in quantifier_list:  # Get all '∀' quantifiers
                # if q.getName() == fms.GlobalConstants.fa: quant_options.append(str(q))
                if q.getName() == fms.GlobalConstants.fa: quant_options.append(q)
            if quant_options == []:
                error_msg = 'Universal quantifiers not found.' \
                            '\nUniversal particularization \ncan not be applied.'
                return False, error_msg, None
        else:
            for q in quantifier_list:  # Get all '∃' quantifiers
                # if q.getName() == fms.GlobalConstants.ex: quant_options.append(str(q))
                if q.getName() == fms.GlobalConstants.ex: quant_options.append(q)
            if quant_options == []:
                error_msg = 'Existential quantifiers not found.' \
                            '\nExistential particularization \nan not be applied.'
                return error_msg, None

        # if len(quant_options) == 1:  # Just one same-type-quantifier in the formula
        #     # r, msg, new_line = self.apply_part_rule_sel_term(line, None, options[0])
        #     r, msg, new_line = self.apply_part_rule_sel_term(line, user_response)
        #     return r, msg, new_line
        # else:
        return True, '', quant_options

    # -----------------------------------------------------------------------------
    def apply_particularization_rule(self, form, selected_line_index, selected_quant, selected_term,
                                     proof_line_list, forbidden_lines):

        quant_name = selected_quant.getName()
        quant_var = selected_quant.getVar()
        # print(f'quant_name: {quant_name}')
        # print(f'quant_var: {quant_var}')

        # print(f'forbidden_lines: {forbidden_lines}')

        tools = UsefullTools()
        proof_lines_copy = copy.deepcopy(proof_line_list)
        allowed_lines = tools.remove_forbidden_lines(forbidden_lines, proof_lines_copy)
        # print(f'allowed_lines: {allowed_lines}')
        allowed_lines = self.remove_rule_references(allowed_lines)
        # print(f'allowed_lines: {allowed_lines}')

        #
        # print(f'self.ex_particularizations: {self.ex_particularizations}')
        #
        # first_order_form = proof_lines_copy[selected_line_index]

        first_order_form = copy.deepcopy(form)
        # print(f'first_order_form: {first_order_form} - type: {type(first_order_form)}')
        line = self.remove_rule_references(proof_line_list)[selected_line_index]
        # print(f'line: {line}')
        if quant_name == fms.GlobalConstants.ex:
            r, msg = self.apply_ex_particularization_rule(first_order_form, selected_line_index,
                                                          quant_var, selected_term,
                                                          line, allowed_lines)

        elif quant_name == fms.GlobalConstants.fa:
            # print("FA")
            r, msg = ddi.apply_universal_particularization(quant_var, selected_term,
                                                           first_order_form, allowed_lines)
        else:
            r = False
            error_message = 'Wrong quantifier selected.'
            return r, error_message, None

        if not r:
            return r, msg, None
        else:
            new_first_order_form = first_order_form
            # print(f'new_first_order_form (antes): {new_first_order_form}')
            new_first_order_form.removeQuantifier(selected_quant)
            # print(f'new_first_order_form (depois): {new_first_order_form}')

            scope = new_first_order_form.getScope()
            # print(f'scope: {scope}')
            gts = new_first_order_form.getQuantifiers()
            # print(f'gts: {gts}')

            if gts == []:
                new_first_order_form = scope
                return r, msg, new_first_order_form
            else:
                return r, msg, new_first_order_form

    # -----------------------------------------------------------------------------
    def apply_ex_particularization_rule(self, first_order_form, selected_line_index, quant_var, selected_term,
                                        line, allowed_lines):

        if selected_line_index not in [p[0] for p in self.ex_particularizations if True]:
            r, msg = ddi.apply_exist_particularization(quant_var, selected_term, first_order_form, allowed_lines)
            if not r:
                return r, msg
            else:
                self.ex_particularizations.append((selected_line_index, selected_line_index + 1, selected_term))

                # print(f'self.ex_particularizations: {self.ex_particularizations}')
                return True, ''
        else:
            error_message = 'The formula < ' + str(line) + \
                            ' > has been used before \nin existential particularization.' \
                            '\nThis rule can not be applied \ntwice to the same formula.'
            return False, error_message

    # -----------------------------------------------------------------------------
    def apply_univ_generalization_rule(self, form, proof_line_list,
                                       selected_var, selected_term):

        if type(form) is fms.Fof:
            q_vars = form.getQuantVars()
        else:
            q_vars = []

        # print(f'q_vars: {q_vars}')

        # var_options = fms.GlobalConstants.list_of_vars
        # print(f'var_options: {var_options}')
        # term_options = fms.GlobalConstants.list_of_terms
        # print(f'term_options: {term_options}')

        # if rule_nick == 'GU_lr':
        # if user_input:
        #     user_input = 1
        #     return user_resp, user_input, '', [var_options, term_options]  # User must select a var and a term
        # else:
        #     # selected_var_index = user_response[1][0]
        #     # selected_term_index = user_response[1][1]
        #     # selected_var = var_options[selected_var_index]
        #     # selected_term = term_options[selected_term_index]
        #     # print(f'selected_var: {selected_var}')
        #     # print(f'selected_term: {selected_term}')
        prem_and_hyp = self.remove_rule_references(self.argument_premisses)
        # prem_and_hyp = self.argument_premisses
        for p in self.list_of_hypothesis:
            prem_and_hyp.append(proof_line_list[p])

        r, msg, new_form = ddi.apply_univ_gener(form, selected_var, selected_term, q_vars, prem_and_hyp,
                                                self.ex_particularizations)
        if not r:
            return r, msg, None
        else:
            # print(f'new_form: {new_form}')
            quant_symbol = fms.GlobalConstants.fa
            new_form = self.continue_to_update(quant_symbol, new_form, selected_var)
            return r, msg, new_form

    ## -----------------------------------------------------------------------------
    def apply_exist_generalization_rule(self, user_response, form):

        # print(f'form: {form}-  type: {type(form)}')
        # print(f'>>>>>>>>>>>>>>>>>user_response: {user_response}')

        user_input, user_resp_total, _ = user_response

        if len(user_resp_total) == 2:
            selected_var, selected_term = user_resp_total
            # print(f'selected_var: {selected_var}')
            # print(f'selected_term: {selected_term}')

            tools = UsefullTools()
            terms = tools.get_scope_terms(form, [])
            i = terms.count(selected_term)  # Number of occurrences of the term
            positions = []

            while i > 0:
                positions.append(i)
                i = i - 1
            positions.reverse()
            tools = UsefullTools()
            term_to_replace_options = tools.get_combinations(tools.powerset(positions))
            # print(f'term_to_replace_options: {term_to_replace_options}')

            if not term_to_replace_options:
                user_input = 0
                error_message = "The chosen term is not in the formula."
                return False, error_message, user_input, (None, None)
            elif len(term_to_replace_options) > 1:
                #User must select positions where term must be replaced
                user_input = 2
                return True, ' ', user_input, (["Select the terms to replace, please."],
                                               term_to_replace_options, selected_var, selected_term)
            else:
                user_input = 1
                return True, ' ', user_input, (term_to_replace_options, selected_var, selected_term)

        else:

            selected_term_to_replace,selected_var,selected_term = user_resp_total
            # print(f'selected_var: {selected_var}')
            # print(f'selected_term: {selected_term}')
            # print(f'selected_terms_to_replace: {selected_term_to_replace}')

            if type(form) is fms.Fof:
                q_vars = form.getQuantVars()
            else:
                q_vars = []

            # print(f'q_vars: {q_vars}')

            # The selected term is replaced by the new var in formula
            s_index_terms = selected_term_to_replace.split(' e ')
            # print(f's_index_terms: {s_index_terms} - type {s_index_terms}')
            index_terms = [int(i) for i in s_index_terms]
            # print(f'index_terms: {index_terms}')

            r, msg, new_form = ddi.apply_exist_gener(selected_var,
                                                     q_vars, selected_term, index_terms, form,
                                                     index_terms)

            # print(f'new_form: {new_form}')
            # r, msg, new_form = self.apply_gen_exist_rule(quant_symbol, selected_var, q_vars, selected_term, form,
            #                                              terms_to_replace)
            # print(f'new_form2: {new_form}')
            quant_symbol = fms.GlobalConstants.ex
            new_form = self.continue_to_update(quant_symbol, new_form, selected_var)
            # print(f'new_form3: {new_form}')
            return r, user_input, msg, new_form

    # -----------------------------------------------------------------------------
    # def apply_gen_exist_rule(self, quant_symbol, selected_var, q_vars, term_selected, form, terms_to_replace):
    #
    #     s_index_terms = terms_to_replace.split(' e ')
    #     index_terms = [int(i) for i in s_index_terms]
    #
    #     r, msg, new_form = ddi.apply_exist_gener(selected_var, q_vars, term_selected, index_terms, form, index_terms)
    #     if not r:
    #         return r, msg, None
    #     else:
    #         new_form = self.continue_to_update(quant_symbol, form, selected_var)
    #         print(f'new_form2: {new_form}')
    #         return r, msg, new_form

    # -----------------------------------------------------------------------------
    def continue_to_update(self, quant_symbol, new_form, new_var):

        new_quant = fms.Quant(quant_symbol, new_var)

        if type(new_form) is fms.Fof:
            new_form.insertQuantifier(new_quant)
            # print(f'new_quant: {new_quant}')
            new_formula = new_form
            return new_formula
        else:
            new_formula = fms.Fof([new_quant], new_form)
            return new_formula

    # # -----------------------------------------------------------------------------
    # def apply_predicate_equivalence_rule(self, rule, selected_proof_line_indexes,
    #                                      proof_line_list):
    #     # To user predicates rules, just one line must be selected
    #     rule_name = rule.getName()
    #     rule_nick = rule.getNick()
    #
    #     index = selected_proof_line_indexes[0]  # just one line can be selected
    #     selected_line = proof_line_list[index]
    #     # print(f'selected_line: {selected_line} - type: {type(selected_line)}')
    #     form = self.remove_rule_reference(selected_line)
    #     # print(f'form: {form} - type: {type(form)}')
    #
    #     if (rule_nick == 'DME_rl') or (rule_nick == 'DMU_rl'):
    #         r, msg, new_line = self.apply_deMorgan_right_to_left(form, rule_name)
    #     elif (rule_nick == 'DME_lr') or (rule_nick == 'DMU_lr'):
    #         r, msg, new_line = self.apply_deMorgan_left_to_right(form, rule_name)
    #     else:
    #         msg = 'THE SELECTED RULE CAN NOT BE \nAPPLIED TO PREDICATES. \nTHE RULE <' \
    #               + rule_name + '>\nCAN NOT BE APPLIED.' + '\nPLEASE, TRY IT AGAIN.'
    #         new_line = ' '
    #         r = False
    #
    #     user_input = 0
    #
    #     return r, msg, user_input, new_line

    # -----------------------------------------------------------------------------
    def apply_predicate_equivalence_rule2(self, rule, form):

        # To user predicates rules, just one line must be selected
        rule_name = rule.getName()
        rule_nick = rule.getNick()

        # index = selected_proof_line_indexes[0]  # just one line can be selected
        # selected_line = proof_line_list[index]
        # # print(f'selected_line: {selected_line} - type: {type(selected_line)}')
        # form = self.remove_rule_reference(selected_line)
        # print(f'form: {form} - type: {type(form)}')

        if (rule_nick == 'DME_rl') or (rule_nick == 'DMU_rl'):
            r, msg, new_line = self.apply_deMorgan_right_to_left(form, rule_name)
        elif (rule_nick == 'DME_lr') or (rule_nick == 'DMU_lr'):
            r, msg, new_line = self.apply_deMorgan_left_to_right(form, rule_name)
        else:
            msg = 'THE SELECTED RULE CAN NOT BE \nAPPLIED TO PREDICATES. \nTHE RULE <' \
                  + rule_name + '>\nCAN NOT BE APPLIED.' + '\nPLEASE, TRY IT AGAIN.'
            new_line = ' '
            r = False

        # user_input = 0
        return r, msg,  new_line


    # # -----------------------------------------------------------------------------
    def apply_deMorgan_right_to_left(self, form, rule_name):
        if type(form) is fms.Fof:
            if type(form.getScope()) is fms.Form1:
                r, msg, new_line = pred.applyPredRule(form)
                return r, msg, new_line
            else:
                msg = 'THE FORMULA IN THE SCOPE OF \nQUANTIFIER(S) DO NOT START WITH "~". \nTHE RULE <' \
                      + rule_name + '>\nCAN NOT BE APPLIED.' + '\n PLEASE, TRY IT AGAIN.'
                return False, msg, None
        elif type(form) is fms.Form1:
            opnd1 = form.getOpnd1()
            r, msg, new_form = self.apply_deMorgan_right_to_left(opnd1, rule_name)
            if r:
                new_line = fms.Form1(fms.GlobalConstants.c_not, new_form)
                return r, msg, new_line
            else:
                return r, msg, None
        else:
            msg = 'THE FORMULA IS NOT A fof. \nTHE RULE <' \
                  + rule_name + '>\nCAN NOT BE APPLIED.' + '\n PLEASE, TRY IT AGAIN.'
            return False, msg, None

    # # -----------------------------------------------------------------------------
    def apply_deMorgan_left_to_right(self, form, rule_name):
        if type(form) is fms.Form1:
            opnd1 = form.getOpnd1()
            if type(opnd1) is fms.Fof:
                r, msg, new_line = pred.applyNotPredRule(form)
                # print(f'r: {r} new_line: {new_line} ')
                return r, msg, new_line
            elif type(opnd1) is fms.Form1:
                opnd1 = form.getOpnd1()
                r, msg, new_form = self.apply_deMorgan_left_to_right(opnd1, rule_name)
                # print(f'r: {r} new_form: {new_form} - type: {type(new_form)}')
                if r:
                    new_form1 = fms.Form1(fms.GlobalConstants.c_not, new_form)
                    # print(f'new_form1: {new_form1}')
                    return r, msg, new_form1
                else:
                    return r, msg, None
        else:
            msg = 'THE FORMULA IS NOT A NEGATION OF A Fof. \nTHE RULE <' + rule_name + \
                  '>\nCAN NOT BE APPLIED.' + '\n PLEASE, TRY IT AGAIN.'
            return False, msg, form

    # -----------------------------------------------------------------------------

    def check_for_success(self, new_line):

        # if self.conclusion == fms.GlobalConstants.cnf:
        #     if self.checkForCNF(new_line):
        #         return True # If the formula is in a normal form, returns
        #         # else continue the proving process
        # if self.conclusion == fms.GlobalConstants.dnf:
        #     if self.checkForDNF(new_line):
        #         return True # If the formula is in a normal form, returns
        #         # else continue the proving process


        if new_line == self.argument_conclusion:
            if len(self.list_of_hypothesis) != 0:
                error_message = 'You got to the conclusion, \n\n' \
                                'but did not remove the last Temporary Hypothesis yet.\n\n' \
                                'It must be removed first!'
                return False, error_message
            else:
                #         self.stopClock()
                #         self.saveSolution('FINAL')
                #         # self.printProofTable()
                #         # print('solution saved')
                #         # self.loadSolution()
                message = 'DEMONSTRATION ENDED SUCCESSFULLY.'
                return True, message
        else:
            return False, ''

    # -----------------------------------------------------------------------------
    def print_proof_lines(self, proof_lines):

        i = 0
        l = len(proof_lines)
        while i < l:
            line, rule = proof_lines[i]
            print(f'({i}) {line} - {rule}')
            i += 1
        return


# -----------------------------------------------------------------------------
class UsefullTools():

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        self.input_l = 0

    # -----------------------------------------------------------------------------
    def insert_spaces(self, input_string):
        cnt = fms.GlobalConstants()

        input_string = input_string.replace(cnt.fa, ' ' + cnt.fa + ' ')  # Insert a space before and after 'fa'
        input_string = input_string.replace(cnt.ex, ' ' + cnt.ex + ' ')  # Insert a space before and after 'ex'
        input_string = input_string.replace(cnt.c_not, ' ' + cnt.c_not + ' ')  # Insert a space before and after 'not'
        input_string = input_string.replace('&', ' ' + cnt.c_and + ' ')  # Insert a space before and after ',' (AND)
        input_string = input_string.replace('^', ' ' + cnt.c_and + ' ')  # Insert a space before and after ',' (AND)
        input_string = input_string.replace('|', ' ' + cnt.c_or + ' ')  # Insert a space before and after '|' (OR)
        input_string = input_string.replace('v', ' ' + cnt.c_or + ' ')  # Insert a space before and after '|' (OR)
        input_string = input_string.replace('(', ' ( ')  # Insert a space before and after '('
        input_string = input_string.replace(')', ' ) ')  # Insert a space before and after ')'
        input_string = input_string.replace('~', ' ' + cnt.c_not + ' ')  # Insert a space before and after '~'
        input_string = input_string.replace('<->',
                                            ' ' + cnt.c_iff + ' ')  # Insert a space before and after '<->'. The previous line
        # changes original occurrences of '<->
        input_string = input_string.replace('->', ' ' + cnt.c_if + ' ')  # Insert a space before and after '->'
        input_string = input_string.replace(',', ' , ')  # Insert a space before and after ',' in a list of premisses
        input_string = input_string.replace('T', cnt.true)  # Tautology
        input_string = input_string.replace('⊥', cnt.false)  # Contradiction
        input_string = input_string.replace('cnf', cnt.cnf)  # CNF
        input_string = input_string.replace('dnf', cnt.dnf)  # DNF
        for c in cnt.list_of_functs:
            input_string = input_string.replace(c, ' ' + c)  # Insert a space before a functor symbol

        return input_string

    # -----------------------------------------------------------------------------
    def get_options(self, ind_form_list):
        options = []
        for (ind, form) in ind_form_list:
            options += [str(form) + ' - AT POS ' + str(ind)]
        return options

    # # -----------------------------------------------------------------------------
    # def check_number_of_selected_lines(self, rule, selected_proof_lines):
    #     if len(rule.getPremis()) != len(selected_proof_lines):
    #         return False, "Wrong number of selected proof_lines."
    #     else:
    #         return True, ''

    # # -----------------------------------------------------------------------------
    # def check_selected_lines(self, selected_proof_lines, forbidden_lines):
        '''
        Check if just one line was selected and if it is not forbidden

        :param selected_proof_lines: a list of the selected lines
        :param forbidden_lines: the list of forbidden lines (those that were
            marked when a hypothesis was removed
        :return: True/False and an error message
        '''

        # r, msg = self.check_if_just_one_line_selected(selected_proof_lines)
        #
        # if not r:
        #     return r, msg
        # else:
        #     r1, msg = self.check_if_the_lines_are_forbidden(selected_proof_lines,
        #                                                     forbidden_lines)
        #     if not r1:
        #         return r1, msg
        #     else:
        #         return True, ''

    # -----------------------------------------------------------------------------
    def check_if_the_lines_are_forbidden(self, selected_lines, forbidden_lines):
        '''
        Check if the  selected lines are forbidden.
        A proof line is forbidden if it is between
        a hypothesis and a consequent, after the
        hypothesis is removed by application
        of the appropriate inference rule.
        :param selected_lines:
        :param forbidden_lines:
        :return: True/False and an error message
        '''
        for l in selected_lines:
            if l in forbidden_lines:
                errorMessage = 'The line < ' + str(l) + ' > was selected ' + \
                               '\nBut it is forbidden!'
                return False, errorMessage,

        return True, ''

    # # -----------------------------------------------------------------------------
    # def check_if_just_one_line_selected(self, lines):
    #     '''
    #     Check if just one line was selected.
    #     This used necessarily in proving equivalences.
    #     :param lines: a list of the selected lines
    #     :return: True/False and an error message
    #     '''
    #     if len(lines) == 1:
    #         return True, ''
    #     else:
    #         errorMessage = 'Select just one proof line, please.'
    #         return False, errorMessage

    # -----------------------------------------------------------------------------
    def remove_parenthesis(self, t_list):
        """
                Remove the characters '(' e ')', from the input string, as in ['~', 'p', 'v', '(', 'p', '->', 'q', ')']
                producing the lists ['~', 'p', 'v', ['p', '->', 'q']]

            :param t_list: an input character list
            :return: a nes list, without parenthesis
            """
        # print(f't_list: {t_list}')
        # print(f'len(t_list): {len(t_list)}')

        if t_list == []:  # An empty list
            return True, '', t_list

        elif t_list.count('(') != t_list.count(')'):
            error_message = 'Different number of ( and ).'
            return False, error_message, []
        elif (t_list.count('(') == 0) or (t_list.count(')') == 0):
            if len(t_list) > 1:
                return True, '', t_list
            else:
                return True, '', t_list[0]
        else:
            # Searches for the first occurence of a par (   )
            terms_bet_par, ind_in, ind_f = self.get_terms_between_parenthesis(t_list)
            # Delete the expression between parenthesis in t_list and the quantifier in position ind_in-1
            # print(f'ind_in: {ind_in}')
            # print(f'ind_f: {ind_f}')
            # print(f'terms_bet_par: {terms_bet_par}')
            del (t_list[ind_in:ind_f])
            # print(f't_list: {t_list}')

            if len(terms_bet_par) >= 1:
                t_list.insert(ind_in, terms_bet_par)

            # print(f't_list_final: {t_list} - len: {len(t_list)}')

            if len(t_list) == 1:  # t_list contains only one tuple: "( a v b )', for ex.
                return True, '', t_list[0]
            else:
                r, msg, t_list2 = self.remove_parenthesis(t_list)
                return r, msg, t_list2

    # -----------------------------------------------------------------------------
    def get_terms_between_parenthesis(self, t_list):
        """
        sub_list: terms between parenthesis
        t_list: original list withou terms between parenthesis
        ind_in: position of first parenthesis in t_list

        """
        first_occr = t_list.index(')')  # First occurence of ')'
        r_list = t_list[first_occr::-1]
        # Last occurance of '(' before the first ')'
        last_occr = r_list.index('(')
        sub_list = t_list[first_occr - last_occr + 1:first_occr]
        # print(f'sub_list: {sub_list}')
        ind_in = first_occr - last_occr  # Begining of the sub_list
        ind_f = first_occr + 1  # Ending of the sub_list

        return sub_list, ind_in, ind_f

    # -----------------------------------------------------------------------------
    def input_formula(self,input_formula):
        """

        """

        new_formula = input_formula
        r, msg, prepared_new_formula = self.prepare_new_formula(new_formula)

        return r, msg, prepared_new_formula

    # -----------------------------------------------------------------------------
    def prepare_new_formula(self, new_formula):

        tools = UsefullTools()
        new_formula_s = tools.insert_spaces(new_formula)
        # print(f'new_formula_s: {new_formula_s}')
        list_new_formula_s = new_formula_s.split()
        # Variables in predicates must be separated by COMMAS WITHOUT spaces between it
        list_form = list(
            filter((',').__ne__, list_new_formula_s))  # remove all occurrences of ',' from the input_string
        # print(f'list_form: {list_form}')

        r, msg, prep_formula = tools.remove_parenthesis(list_form)
        # print(f'prep_formula: {prep_formula} - type: {type(prep_formula)}')

        r, error_message, rep_formula = fms.generate_represent(prep_formula)

        # print(f'r: {r}')
        # print(f'rep_formula: {rep_formula} - type: {type(rep_formula)}')

        return r, error_message, rep_formula

    # -----------------------------------------------------------------------------
    def get_combinations(self, tuples):
        """
                                 Generates all combinations of the elements. For exemple, if  S = {2, 5, 10}
                                     it produces {{}, {2}, {5}, {10}, {2, 5}, {2, 10}, {5, 10}, {2, 5, 10}}.
                    """
        options = []
        for t in tuples:
            if len(t) > 0:
                option = ' e '.join(str(i) for i in t)
                options.append(option)
        return options

    # -----------------------------------------------------------------------------
    def powerset(self, list):
        """
            Generates all combinations of the elements. For exemple, if  S = {2, 5, 10}
            it produces {{}, {2}, {5}, {10}, {2, 5}, {2, 10}, {5, 10}, {2, 5, 10}}.
        """
        return chain.from_iterable(combinations(list, r) for r in range(len(list) + 1))

    # -----------------------------------------------------------------------------
    def get_scope_terms(self, form, otherVars):
        # print(f'form: {form}: type(form): {type(form)}')
        # print(f'otherVars: {otherVars}')
        if type(form) is fms.Fof:
            vars1 = self.get_scope_terms(form.getScope(), otherVars)
            # print(f'vars1: {vars1}')
            return vars1 + otherVars
        elif type(form) is fms.Pred:
            vars = form.getPredVars()
            return vars + otherVars
        elif type(form) is fms.Form1:
            vars1 = self.get_scope_terms(form.getOpnd1(), otherVars)
            return vars1
        elif type(form) is fms.Form2:
            vars1 = self.get_scope_terms(form.getOpnd1(), otherVars)
            vars2 = self.get_scope_terms(form.getOpnd2(), vars1)
            return vars2
        else:
            return otherVars

    # -----------------------------------------------------------------------------
    @staticmethod
    def remove_forbidden_lines(forbidden_lines, proof_lines):
        """ Remove forbidden  lines from proof_lines list """
        allowed = []

        i = 0
        while i < len(proof_lines):
            if i in forbidden_lines:
                pass
            else:
                allowed.append(proof_lines[i])
            i += 1
        return allowed

    # -----------------------------------------------------------------------------
    def import_list(self, path, filename):
        '''
        Imports a list of problems (arguments) from .TXT file
        Premisses must be separated by by SPACE-COMMA-SPACE.
        Conjunction operator is & and disjunction operator is | (with spaces before and after them)
        The last proposition must be the conclusion

        Parameters:
            path: the path to the file
            filename:
        '''

        # self.resetApp()
        mraris_home_dir = '/home/cedric/workspace/plato-env/mrAris/'
        PROBLEMS_dir = mraris_home_dir + 'PROBLEMS'
        SOLUTIONS_dir = mraris_home_dir + 'SOLUTIONS'
        ZIP_dir = mraris_home_dir + 'ZIP'

        dir_separator = '/'

        base = os.path.basename(filename)  # Get only the name of the file
        problem_list_name = base.split('.')[0]  # Get the name of the problem list
        # fName = os.path.splitext(base)[0] # Get the name of the file, without extension

        proofDir = SOLUTIONS_dir + dir_separator + problem_list_name  # Includes problemListName in the PROOFS dir name
        print(f'base: {base}')
        print(f'problem_list_name: {problem_list_name}')
        print(f'profDir: {proofDir}')

        if not os.path.isdir(proofDir):
            os.mkdir(proofDir)  # Create a folder named as the problem list name
        else:
            pass  # The folder named as the problem list name exists already

        file = (path, '', problem_list_name)  # base = only the name of the file
        with open(os.path.join(path, filename), 'r', encoding='utf8') as f:
            list_of_problems = f.read().splitlines()  # Returns a list of lines

        list_of_problems = self.remove_comments(list_of_problems)
        return list_of_problems

    # -----------------------------------------------------------------------------
    def remove_comments(self, lines):
        '''
            Comments are lines started by the character '#'.
            They must be removed from the input file.
            Empty lines are also removed
        '''

        lines = [l for l in lines if len(l) != 0]
        lines = [l for l in lines if l[0] != '#']
        return lines

# -----------------------------------------------------------------------------

    def is_literal(self, formula):
        if type(formula) is fms.Form:  # p
            return True
        elif type(formula) is fms.Form1:  # ~p
            if type(formula.opnd1) is fms.Form:
                return True
            else:
                return False
        else:
            return False

    # -----------------------------------------------------------------------------
    def is_cnf(self, formula):

        # print(f"Formula: {formula} - type: {type(formula)}")
        l_conj = self.get_conjunct_list(formula)

        # l = tls.is_cnf(ind_form_list)
        # for i in l_conj:
        #     print(f"i: {i}")

        if len(l_conj) == 1:
            if self.is_literal(l_conj[0]):
                return True
            else:
                return False

        r = True
        for conj in l_conj:
            # print(f" conj: {conj}")
            l_disj = self.get_disjunct_list(conj)
            for d in l_disj:
                # print(f" d: {d}")
                if self.is_literal(d): r = True and r
                else:
                    l_conj_d = self.get_conjunct_list(d)
                    # print(f" l_conj_d: {l_conj_d}")
                    if l_conj_d:
                        # print("FALSE")
                        r = False
                    else:
                        r = True and r

        return r

    # -----------------------------------------------------------------------------
    def is_dnf(self, formula):

        # print(f"Formula: {formula} - type: {type(formula)}")
        l_disj = self.get_disjunct_list(formula)

        # l = tls.is_cnf(ind_form_list)
        # for i in l_disj:
        #     print(f"i: {i}")

        if len(l_disj) == 1:
            if self.is_literal(l_disj[0]):
                return True
            else:
                return False

        r = True
        for disj in l_disj:
            # print(f" conj: {conj}")
            l_conj = self.get_conjunct_list(disj)
            for c in l_conj:
                # print(f" d: {d}")
                if self.is_literal(c):
                    r = True and r
                else:
                    l_disj_d = tls.get_disjunct_list(c)
                    # print(f" l_conj_d: {l_conj_d}")
                    if l_disj_d:
                        # print("FALSE")
                        r = False
                    else:
                        r = True and r

        return r



# -----------------------------------------------------------------------------
    def get_conjunct_list(self, form):

        if self.is_literal(form):
            return [form]
        elif type(form) is fms.Form2:
            # print("form2")
            opnd1 = form.getOpnd1()
            # print(f"opnd1: {opnd1}")
            opnd2 = form.getOpnd2()
            # print(f"opnd2: {opnd2}")

            if form.getOper() == fms.GlobalConstants.c_and:
                l1 = self.get_conjunct_list(opnd1)
                # print(f"l1: {l1}")
                l2 = self.get_conjunct_list(opnd2)
                # print(f"l2: {l2}")
                return l1+l2
            else:
                return [form]
        else:
            return []

# -----------------------------------------------------------------------------
    def get_disjunct_list(self, form):

        if self.is_literal(form):
            return [form]
        elif type(form) is fms.Form2:
            # print("form2")
            opnd1 = form.getOpnd1()
            # print(f"opnd1: {opnd1}")
            opnd2 = form.getOpnd2()
            # print(f"opnd2: {opnd2}")

            if form.getOper() == fms.GlobalConstants.c_or:
                l1 = self.get_disjunct_list(opnd1)
                # print(f"l1: {l1}")
                l2 = self.get_disjunct_list(opnd2)
                # print(f"l2: {l2}")
                return l1+l2
            else:
                return [form]
        else:
            return []


# -----------------------------------------------------------------------------
if __name__ == '__main__':

    tls = UsefullTools()
    pv = Prover()

    formula0 = "0 - ~p  ⊢ CNF"
    formula1 = "0 - p ^ s ⊢ CNF"
    formula2 = "0 - p ^ (p ^ r) ⊢ CNF"
    formula3 = "0 - p ^ (p ^ r) ^ q ⊢ CNF"
    formula4 = "0 - p ^ (p v (r ^ s)) ^ (q v s) ⊢ CNF"
    formula5 = "0 - p v (p ^ r) v (q ^ s) ⊢ DNF"
    formula6 = "0 - ~p ∨ ~q ⊢ DNF"

    pv.input_an_argument(formula6)
    nformula = pv.remove_rule_reference(pv.argument_premisses[0])

    # ind_form_list = fms.index_form(0, nformula)
    print(f"premiss: {nformula}")
    # print(f"ind_form_list: {ind_form_list}")



    r = tls.is_dnf(nformula)
    print(f"r: {r}")

    # l = tls.get_disjunct_list(nformula)
    # for i in l:
    #     print(f"i: {i}")

