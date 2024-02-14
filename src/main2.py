#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Apr 29 08:30:41 2021

@author: cedric
"""

import tools
import forms as fms


list_of_problems =\
    [# Proving inferences
'0 - p  → q , p ⊢ (q v p)',
'1 - p → q , ~q ⊢ ~p v q',
# '2 - p → q , q → s ⊢ p → s',
'2 - p , q ⊢ p ^ q',
# Proving hypothesis
'3 - ~~p → q ⊢ p -> q',
'4 - p → ~~q ⊢ p -> q',
'5 - p → ~(p ^ r)  ⊢ p →  (~p v ~r)',
'6 - ~~p ⊢ p',
'7 - ~p ⊢ ~~~p',
#
# Proving equivalences
'8 - ~~p → q ⊢ p -> q',
'9 - p → ~~q ⊢ p -> q',
'10 - p → ~(p ^ r)  ⊢ p →  (~p v ~r)',
'11 - ~~p ⊢ p',
'12 - ~p ⊢ ~~~p',
#
# Proving predicates
'13 - ∼p(a) ⊢ ∼∀xp(x)',
'14 - ∃x∀y(p(x,y) v q(x,y)) ⊢ p(a,a) v q(a,a)',
'15 - ∀x(p(x) → q(x)) , ∀x(q(x) → r(x)) ⊢ ∀x(p(x) → r(x))',
'16 -  ∀x(p(x) ∧ q(x)) ⊢ ∀xp(x) ∧ ∀xq(x)',
'17 - ~∀xp(x)  ⊢  ∃x~p(x)',
'18 - ~∃xp(x)  ⊢  ∀x~p(x)',
'19 - ∀xp(x)  ⊢ ∀xp(x)',

# Proving equivalences
'20 - ~~p ⊢ CNF ',
'21 - p ⊢ DNF ',
'22 - p ⊢ CNF ',
'23 - ~p ⊢ CNF '
#
]


# -----------------------------------------------------------------------------
#seleciona uma opção (de uma lista), exibindo um label
def select_option(label, options):
    i = 0
    f = len(options)
    while i < f:
        print(f'{i} - {options[i]}')
        i += 1
    selection = int(input(f'Select a {label}, please: '))
    print(f'selection: {selection}')
    return options[selection]

# -----------------------------------------------------------------------------

def start():
    pv = tools.Prover()
    tls = tools.UsefullTools()

    # st.session_state.status_message = (0, "")
    # type_selected, rule_index = st.session_state.selected_rule
    # sel_lines = st.session_state.selected_lines

    #list_of_problems = tls.import_list("/home/cedric/workspace/plato-env/mrAris/PROBLEMS/","listaTeste1.lpb")

    print("List of problems: ")
    for p in list_of_problems:
        print(p)

    # print('INFERENCE RULES')
    # for r in pv.rti:
    #     print(pv.rti[r])
    
    # print('EQUIVALENCE RULES')
    # for r in pv.rte:
    #     print(pv.rte[r])
    
    # print('PREDICATE INFERENCE RULES')
    # rtp_i, rtp_e = pv.rtp
    # for r in rtp_i:
    #     print(rtp_i[r])
    
    # print('PREDICATE EQUIVALENCE RULES')
    # for r in rtp_e:
    #     print(rtp_e[r])



    # initializes
    pb_index = int(input('Qual problema quer resolver? : '))  # regra selecionada
    r, msg = pv.input_an_argument(list_of_problems[pb_index])
    if not r:
        print(f"Proving argument: ", msg)


    # start proving loop

    # Print proof line
    print(f'\nProving context \n----------------------------\n')
    pv.print_proof_lines(pv.proof_lines)
    # print(f'List_of_hypothesis: {pv.list_of_hypothesis}')
    print(f'\n----------------------------\n')

    r = 1
    while r:
        # -----------------------------------------------------------------------------
        rule_types = {'0': 'HYP', '1': 'INF', '2': 'EQ', '3': 'PRED_I', '4': 'PRED_E'}
        type_selected = input(
            'Digite tipo da regra a ser usada (0 - HYP, 1 - INF, 2 - EQ, 3 - PRED_I, 4 - PRED_E): ')  # tipo da regra
        rule_type = rule_types[type_selected]
        sel_rule = int(input('Digite a regra a ser usada: '))  # regra selecionada

        # select lines and rule
        selected_proof_line_indexes = []
        j = 1
        while j:
            proof_line = int(input('Digite uma linha a ser usada. <- 1 encerra>: '))
            if proof_line < 0:
                break
            else:
                selected_proof_line_indexes.append(proof_line)

        # print(f'selected_proof_line_indexes: {selected_proof_line_indexes} ')


        total_or_partial = "total" # indicates if the prove takes the whole line or not
        # user_input: indicates user needs to select something
        r, msg, user_input, new_line, proof_line_updated = \
            pv.prove(rule_type, sel_rule, selected_proof_line_indexes, pv.proof_lines, (0, None, total_or_partial))
        # print(f"user_input: {user_input}")
        # print(f"new_line0: {new_line}")


        if not r:
            print(f"ERRO: {msg}")
        else:
            if user_input > 0:
                print(f"rule_type: {rule_type}")
                # if type_selected in ['0', '1']:  # HYP or INF
                if (rule_type == "HYP") or (rule_type == "INF"):
                    ru, error_message, new_formula = tls.input_formula()

                    if not ru:
                        print(f'ERROR: {error_message}')
                    else:
                        r, msg, new_line, proof_line_updated = continue_proving_inference(total_or_partial, pv, rule_type, sel_rule,
                                                            selected_proof_line_indexes, new_formula)
                # elif type_selected == '2':  # EQ
                elif rule_type == "EQ":
                    labels, options = new_line
                    # Select the sub-formula
                    sub_form = select_option(labels[0], options[0])
                    r, msg, new_line, proof_line_updated = continue_proving_equivalence(total_or_partial, pv, rule_type, sel_rule,
                                                          selected_proof_line_indexes, sub_form)
                    print(f"r: {r}")
                else:  # PRED
                    labels, options = new_line
                    if len(options[0]) > 1:  # new_line = (["variable, "term"], [var_options, term_options])
                        selected_term = select_option(labels[0], options[0])
                        r, msg, new_line, proof_line_updated = continue_proving_predicates_1(total_or_partial, labels[0], options[0],pv, rule_type, sel_rule,
                                                               selected_proof_line_indexes, selected_term)
                    else:
                        label = labels[1].replace("term", "term to replace ")
                        selected_sub_term = options[0][0]
                        r, msg, new_line, proof_line_updated = continue_proving_predicates_1(total_or_partial, label, options[1], pv, rule_type, sel_rule,
                                                               selected_proof_line_indexes, selected_sub_term)

        if r:
            print(f'\nProving context \n----------------------------\n')
            pv.print_proof_lines(proof_line_updated)
            # print(f'List_of_hypothesis: {pv.list_of_hypothesis}')
            print(f'\n----------------------------\n')
        else:
            print(f"ERRO: {msg}")

        rf, final_msg = pv.check_for_success(new_line)
        if rf:
            print(final_msg)
            break




# -----------------------------------------------------------------------------
def continue_proving_inference(total_or_partial, pv, type_selected, rule_index, sel_lines, new_formula):

    r, msg, user_input, new_line, proof_line_updated = \
            pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines,
                     (0, new_formula, total_or_partial))

    return r, msg, new_line, proof_line_updated


# -----------------------------------------------------------------------------
def continue_proving_equivalence(total_or_partial, pv, type_selected, rule_index, sel_lines,sub_form):
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, sub_form, total_or_partial))

    return r, msg, new_line, proof_line_updated


# -----------------------------------------------------------------------------
def continue_proving_predicates_1(total_or_partial, label, options, pv, type_selected, rule_index, sel_lines,selected_term):

    selected_var = select_option(label, options)
    r, msg, new_line, proof_line_updated = \
        continue_proving_predicates_2(total_or_partial, pv, type_selected, rule_index, sel_lines, selected_var,selected_term)

    return r, msg, new_line, proof_line_updated


# -----------------------------------------------------------------------------
def continue_proving_predicates_2(total_or_partial, pv, type_selected, rule_index, sel_lines, selected_var, selected_term):
    user_resp = (selected_var, selected_term)
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp, total_or_partial))

    if not r:
        msg = msg + "\n\n This rule cannot be applied here!"
        return r, msg, new_line, proof_line_updated
    else:
        if user_input == 0:
            return r, msg, new_line, proof_line_updated
        elif user_input == 1:
            user_resp = (new_line[0][0], selected_var, selected_term)

            r, msg, user_input, new_line, proof_line_updated = \
                pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp, total_or_partial))
            if r:
                return r, msg, new_line, proof_line_updated
            else:
                return r, msg+ "\n\n This rule cannot be applied here!"

        else:  # user_input = 2
            # print(f"user_input: {user_input}")
            labels, options, selected_var, selected_term = new_line

            terms_to_replace = select_option(labels[0], options)
            r, msg, new_line, proof_line_updated = \
                continue_proving_predicates_3(total_or_partial, pv, type_selected, rule_index, sel_lines,
                                                   selected_var, selected_term,terms_to_replace)

            return r, msg, new_line, proof_line_updated


# -----------------------------------------------------------------------------
def continue_proving_predicates_3(total_or_partial, pv, type_selected, rule_index, sel_lines,
                                  selected_var, selected_term, terms_to_replace):
    user_resp = (terms_to_replace, selected_var, selected_term)
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp,total_or_partial))

    return r, msg, new_line, proof_line_updated

# -----------------------------------------------------------------------------
def check_for_success(pv, new_line):

    tls = tools.UsefullTools()

    conclusion = pv.argument_conclusion
    if conclusion == fms.GlobalConstants.cnf:
        r = tls.is_cnf(new_line)
    elif conclusion == fms.GlobalConstants.dnf:
        r = tls.is_dnf(new_line)
    else:
        # print(f"new_line: {new_line} - type: {type(new_line)}")
        # print(f"conclusion: {conclusion} - type: {type(conclusion)}")
        r = new_line == conclusion
    if (r):
        if len(pv.list_of_hypothesis) != 0:
            error_message = 'You got to the conclusion, \n\n' \
                            'but did not remove the last Temporary Hypothesis yet.\n\n' \
                            'It must be removed first!'
            return False, error_message
        else:
            return True, 'DEMONSTRATION ENDED SUCCESSFULLY!'
    else:
        return False, ''  # Proof not ended

# -----------------------------------------------------------------------------
if __name__ == '__main__':
    start()



