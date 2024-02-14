from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
from .session_exercises_dto import CreateSessionExerciseDtoInput, CreateSessionExerciseDtoOutput
from .apply_rule_dto import DataInputApplyRuleDto, DataOutputApplyRuleDto
import tools
import pickle
from fastapi import Cookie, Request
from exercises import listas_exercises

apply_rule_router = APIRouter()

"""
    DataInputApplyRuleDto docs

    rows: [
     {"content": "p -> q", "methods_used_info":"", "type":"default",},
     {"content": "p -> q", "methods_used_info":"", "type":"default",},
     {"content": "p -> q", "methods_used_info":"", "type":"default",}, 
     {"content": "p -> q", "methods_used_info":"", "type":"default",},
     ] 

    index_selected_rows: [0,1,2,3,4,5,6,7,8,9...] -> São as linhas selecionadas pelo usuario

    selected_rule_data = {
        type: "INF",
        index_selected_rule: 9
    }



    possibilities for output apply rules are: 
        first:  
                DataOutputApplyRuleDto(
                    type_output = "PROVED",
                    message="Congratulations, you successfully proved it",
                    new_line = {"content": "content", "methods_used_info":"1-Add...", "type":"default",}
                    )
        second:

                DataOutputApplyRuleDto(
                    type_output = "CREATED",
                    message="New line created",
                    new_line = {"content": "p → q", "methods_used_info":"1-SHPT", "type":"default",}
                    )

        third:
                DataOutputApplyRuleDto(
                    type_output = "ERROR"
                    message="Error",
                    new_line = {"content": "", "methods_used_info":"", "type":"",}
                    )

"""



from pydantic import BaseModel
from fastapi import HTTPException, FastAPI, Response, Depends
from uuid import UUID, uuid4

from fastapi_sessions.backends.implementations import InMemoryBackend
from fastapi_sessions.session_verifier import SessionVerifier
from fastapi_sessions.frontends.implementations import SessionCookie, CookieParameters


class SessionData(BaseModel):
    id: UUID 
    prover: Any = None
 
    




cookie_params = CookieParameters()

# Uses UUID
cookie = SessionCookie(
    cookie_name="cookie",
    identifier="general_verifier",
    auto_error=True,
    secret_key="DONOTUSE",
    cookie_params=cookie_params,
)
backend = InMemoryBackend[UUID, SessionData]()


class BasicVerifier(SessionVerifier[UUID, SessionData]):
    def __init__(
        self,
        *,
        identifier: str,
        auto_error: bool,
        backend: InMemoryBackend[UUID, SessionData],
        auth_http_exception: HTTPException,
    ):
        self._identifier = identifier
        self._auto_error = auto_error
        self._backend = backend
        self._auth_http_exception = auth_http_exception

    @property
    def identifier(self):
        return self._identifier

    @property
    def backend(self):
        return self._backend

    @property
    def auto_error(self):
        return self._auto_error

    @property
    def auth_http_exception(self):
        return self._auth_http_exception

    def verify_session(self, model: SessionData) -> bool:
        """If the session exists, it is valid"""
        return True
    

verifier = BasicVerifier(
    identifier="general_verifier",
    auto_error=True,
    backend=backend,
    auth_http_exception=HTTPException(status_code=403, detail="invalid session"),
)











list_of_problems_teste =\
    [# Proving inferences
'0 - p  → q , p ⊢ (q v p)',
'1 - p → q , ~q ⊢ ~p',
# '2 - p → q , q → s ⊢ p → s',
'2 - p → q, ⊢ p ^ q',
#
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




def continue_proving_inference(total_or_partial, pv, type_selected, rule_index, sel_lines, new_formula):

    r, msg, user_input, new_line, proof_line_updated = \
            pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines,
                     (0, new_formula, total_or_partial))

    return r, msg, new_line, proof_line_updated




def select_option(options,selection):
    return options[selection]


def continue_proving_equivalence(total_or_partial, pv, type_selected, rule_index, sel_lines,sub_form):
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, sub_form, total_or_partial))

    return r, msg, new_line, proof_line_updated


def continue_proving_pred_equivalence(total_ou_partial, pv, type_selected, rule_index,
                                      sel_lines,sub_formula):

    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, sub_formula, total_ou_partial))

    return r, msg, new_line, proof_line_updated


def continue_proving_predicates_1(label, options, pv, type_selected, rule_index, sel_lines, selected_term):
    selected_var = options[0]
    r, msg, new_line, proof_line_updated = \
        continue_proving_predicates_2(pv, type_selected, rule_index, sel_lines,
                                      selected_var, selected_term)
    return r, msg, new_line, proof_line_updated


def continue_proving_predicates_2(pv, type_selected, rule_index, sel_lines, selected_var, selected_term):

    user_resp = (selected_var, selected_term)
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp, "total"))

    if not r:
        msg = msg + "\n\n This rule cannot be applied here!"
        return r, msg, new_line, proof_line_updated
    else:
        if user_input == 0:
            return r, msg, new_line, proof_line_updated
        elif user_input == 1:
            user_resp = (new_line[0][0], selected_var, selected_term)

            r, msg, user_input, new_line, proof_line_updated = \
                pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp, "total"))
            if r:
                return r, msg, new_line, proof_line_updated
            else:
                return r, msg+ "\n\n This rule cannot be applied here!"

        else:  # user_input = 2
            # print(f"user_input: {user_input}")
            labels, options, selected_var, selected_term = new_line

            terms_to_replace = select_option(labels[0], options)
            r, msg, new_line, proof_line_updated = \
                continue_proving_predicates_3(pv, type_selected, rule_index, sel_lines,
                                              selected_var, selected_term,terms_to_replace)

            return r, msg, new_line, proof_line_updated
        

def continue_proving_predicates_3(pv, type_selected, rule_index, sel_lines,
                                  selected_var, selected_term, terms_to_replace):
    user_resp = (terms_to_replace, selected_var, selected_term)
    r, msg, user_input, new_line, proof_line_updated = \
        pv.prove(type_selected, rule_index, sel_lines, pv.proof_lines, (0, user_resp,"total"))

    return r, msg, new_line, proof_line_updated
    


@apply_rule_router.post("/apply_rule_router/")
async def apply_rule(requests: Request, data: DataInputApplyRuleDto, response: Response) -> DataOutputApplyRuleDto:

    if requests.cookies.get("cookie"):
        session = cookie(requests)
        session_data: SessionData = await backend.read(session)


    
        if session_data is None:
            pv_instance = tools.Prover()
            serialized_instance = pickle.dumps(pv_instance)
            session = uuid4()
            dataSession = SessionData(id=session, prover=serialized_instance)
            session_data = await backend.create(session, dataSession)
            cookie.attach_to_response(response, session)


    else:

            pv_instance = tools.Prover()
            serialized_instance = pickle.dumps(pv_instance)
            session = uuid4()
            dataSession = SessionData(id=session, prover=serialized_instance)
            session_data = await backend.create(session, dataSession)
            cookie.attach_to_response(response, session)


    selected_proof_line_indexes = data.selected_proof_line_indexes
    pb_index = data.pb_index
    list_index = data.list_index
    type_selected = data.type_selected
    sel_rule = data.sel_rule
    input_formula = data.input_formula
    total_or_partial = data.total_or_partial
    selection = data.selection
    options = []

    data_session: SessionData = await backend.read(session)

    pv = pickle.loads(data_session.prover)


    tls = tools.UsefullTools()

    r, msg = pv.input_an_argument(listas_exercises[list_index]["data"][pb_index])

    rule_types = {'0': 'HYP', '1': 'INF', '2': 'EQ', '3': 'PRED_I', '4': 'PRED_E'}

    rule_type = rule_types[type_selected]

    # indicates if the prove takes the whole line or not

    
    r, msg, user_input, new_line, proof_line_updated = \
                pv.prove(rule_type, sel_rule, selected_proof_line_indexes, pv.proof_lines, (0, None, total_or_partial))
    
    

    
    if not r:
        print(f"ERRO: {msg}")
    else:
        if user_input > 0:
            print(f"rule_type: {rule_type}")
            # if type_selected in ['0', '1']:  # HYP or INF
            if (rule_type == "HYP") or (rule_type == "INF"):
                ru, error_message, new_formula = tls.input_formula(input_formula)

                if not ru:
                    print(f'ERROR: {error_message}')
                else:
                    r, msg, new_line, proof_line_updated = continue_proving_inference(total_or_partial, pv, rule_type, sel_rule,
                                                        selected_proof_line_indexes, new_formula)
            # elif type_selected == '2':  # EQ
            elif rule_type == "EQ":
                labels, options = new_line
                # Select the sub-formula
                sub_form = select_option(options[0], selection=selection)
                r, msg, new_line, proof_line_updated = continue_proving_equivalence(total_or_partial, pv, rule_type, sel_rule,
                                                        selected_proof_line_indexes, sub_form)
                print(f"r: {r}")

            elif rule_type == "PRED_E":
                labels, options = new_line
                sub_formula = select_option(options[0], selection=selection)
                r, msg, new_line, proof_line_updated = \
                    continue_proving_pred_equivalence(total_or_partial, pv,
                                                        rule_type,sel_rule,selected_proof_line_indexes,
                                                        sub_formula)
            else:  #rule_type == "PRED_I"
                labels, options = new_line
                selected_term = select_option(options[0], selection=selection)
                r, msg, new_line, proof_line_updated = \
                    continue_proving_predicates_1(labels[1], options[1], pv, rule_type,
                                                    sel_rule,selected_proof_line_indexes,
                                                    selected_term)
                                                           

    lines = []
    for element in proof_line_updated:
        if("ADHY" in element[1]):
            formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"add",}
            lines.append(formate)
        else:
            formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"default",}
            lines.append(formate)
        

    if r:

        output = DataOutputApplyRuleDto(
            type_output = "CREATED",
            message = str(msg),
            lines = lines,
    )
    else:
        output = DataOutputApplyRuleDto(
            type_output = "ERROR",
            message = str(msg),
            lines = lines,
            
    )

        print(f"ERRO: {msg}")

    rf, final_msg = pv.check_for_success(new_line)

    if rf:

        output = DataOutputApplyRuleDto(
        type_output = "PROVED",
        message = str(final_msg),
        lines = lines,
    )

 
    serialized_instance = pickle.dumps(pv)
    dataSession = SessionData(id=session, prover=serialized_instance)
    session_data = await backend.update(session, dataSession)

    #write here


    return output









@apply_rule_router.get("/delete_session")
async def del_session(requests: Request,response: Response):
    if requests.cookies.get("cookie"):
        key = cookie(requests)
        session_data: SessionData = await backend.read(key)
    
        if session_data:
            session_data: SessionData = await backend.delete(key)
            cookie.delete_from_response(response)
            return "deleted session"
        


def filter_new_lines(proof_lines):
    lines = []
    for element in proof_lines:
        if element[1] != "P":
            formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"default",}
            lines.append(formate)
    
    return lines





@apply_rule_router.post("/create_session_exercise")
async def create_session(requests: Request, data: CreateSessionExerciseDtoInput, response: Response):
    pb_index = data.pb_index
    list_index = data.list_index


    if requests.cookies.get("cookie"):
        session = cookie(requests)
        session_data: SessionData = await backend.read(session)
    
        if session_data is None:
            pv_instance = tools.Prover()
            r, msg = pv_instance.input_an_argument(listas_exercises[list_index]["data"][pb_index])
            serialized_instance = pickle.dumps(pv_instance)
            session = uuid4()
            dataSession = SessionData(id=session, prover=serialized_instance)
            session_data = await backend.create(session, dataSession)
            cookie.attach_to_response(response, session)

            lines = []
            for element in pv_instance.argument_premisses:
                formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"default",}
                lines.append(formate)

            s = str(pv_instance.argument_conclusion)
            new_lines = filter_new_lines(pv_instance.proof_lines)
    

            output: CreateSessionExerciseDtoOutput = {
                "premisses": lines, 
                "conclusion":s,
                "new_lines": new_lines,
            }

            return output



        else:
            data_session: SessionData = await backend.read(session)
            pv_instance = pickle.loads(data_session.prover)
            r, msg = pv_instance.input_an_argument(listas_exercises[list_index]["data"][pb_index])
            s = str(pv_instance.argument_conclusion)
            lines = []
            for element in pv_instance.argument_premisses:
                formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"default",}
                lines.append(formate)

            new_lines = filter_new_lines(pv_instance.proof_lines)


            output: CreateSessionExerciseDtoOutput = {
                "premisses": lines, 
                "conclusion":s,
                "new_lines": new_lines,
            }

            return output


    else:

        pv_instance = tools.Prover()
        serialized_instance = pickle.dumps(pv_instance)
        r, msg = pv_instance.input_an_argument(listas_exercises[list_index]["data"][pb_index])
        session = uuid4()
        dataSession = SessionData(id=session, prover=serialized_instance)
        session_data = await backend.create(session, dataSession)
        cookie.attach_to_response(response, session)

        lines = []
        for element in pv_instance.argument_premisses:
            formate = {"content": f"{element[0]}", "methods_used_info":f"{element[1]}", "type":"default",}
            lines.append(formate)

        s = str(pv_instance.argument_conclusion)
        new_lines = filter_new_lines(pv_instance.proof_lines)


        output: CreateSessionExerciseDtoOutput = {
            "premisses": lines, 
            "conclusion":s,
            "new_lines": new_lines,
            
        }

        return output
