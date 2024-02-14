from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
from .selected_form_dto import DataInputGetOptionsSelectedFormDto, DataInputSelectedFormDto, DataOutputGetOutputSelectedFormDto, DataOutputSelectedFormDto, SelectedFormOutputDto
from fastapi import Request
import tools
import pickle
from pydantic import BaseModel
from uuid import UUID, uuid4
from fastapi import Response

from fastapi_sessions.backends.implementations import InMemoryBackend
from fastapi_sessions.session_verifier import SessionVerifier
from fastapi_sessions.frontends.implementations import SessionCookie, CookieParameters

from .apply_rule_route import SessionData, backend, cookie
from exercises import listas_exercises

selected_form_router = APIRouter()
cookie_params = CookieParameters()

# Uses UUID


def options_in_rows(options):
    
    if options[0] == ["a"] or options[0] == []:
        options_rows = []
        for element in options[1]:
            z = {"content": f"{element}", "methods_used_info":"", "type":""}
            options_rows.append(z)

        return options_rows
    

    options_rows = []

    for element in options[0]:
        z = {"content": f"{element}", "methods_used_info":"", "type":""}
        options_rows.append(z)

    return options_rows



def get_options_function(pv,list_index, pb_index, type_selected, sel_rule, selected_proof_line_indexes, total_or_partial):

    r, msg = pv.input_an_argument(listas_exercises[list_index]["data"][pb_index])

    rule_types = {'0': 'HYP', '1': 'INF', '2': 'EQ', '3': 'PRED_I', '4': 'PRED_E'}


    rule_type = rule_types[type_selected]

    # indicates if the prove takes the whole line or not

    print("list_index",list_index, "sel_rule", sel_rule,"type_selected",type_selected, "selected_proof_line_indexes",selected_proof_line_indexes)

    r, msg, user_input, new_line, proof_line_updated = \
                pv.prove(rule_type, sel_rule, selected_proof_line_indexes, pv.proof_lines, (0, None, total_or_partial))   
    


    if not r:
        return r, msg, None
    else:
        if user_input > 0:
            if rule_type == "EQ":
                labels, options = new_line
    
                print(f"r: {r}")

            elif rule_type == "PRED_E":
                labels, options = new_line

            else:  #rule_type == "PRED_I"

                labels, options = new_line

    
    return r, msg, options







@selected_form_router.post("/get_options_selected_form/")
async def get_options_selected_form(requests: Request, data: DataInputGetOptionsSelectedFormDto,response: Response) -> SelectedFormOutputDto:

    selected_proof_line_indexes = data.selected_proof_line_indexes
    pb_index = data.pb_index
    list_index = data.list_index
    type_selected = data.type_selected
    sel_rule = data.sel_rule
    total_or_partial = data.total_or_partial

    if requests.cookies.get("cookie"):
        session = cookie(requests)
        session_data: SessionData = await backend.read(session)

        if session_data is None:
            pv = tools.Prover()
            serialized_instance = pickle.dumps(pv)
            session = uuid4()
            dataSession = SessionData(id=session, prover=serialized_instance)
            session_data = await backend.create(session, dataSession)
            cookie.attach_to_response(response, session)
            r, msg, options = get_options_function(pv,list_index=list_index, 
                                                type_selected=type_selected, 
                                                pb_index=pb_index, sel_rule=sel_rule, 
                                                selected_proof_line_indexes=selected_proof_line_indexes,
                                                total_or_partial=total_or_partial)
        else:
            pv = pickle.loads(session_data.prover)
            r, msg, options = get_options_function(pv,list_index=list_index, 
                                                type_selected=type_selected, 
                                                pb_index=pb_index, sel_rule=sel_rule, 
                                                selected_proof_line_indexes=selected_proof_line_indexes,
                                                total_or_partial=total_or_partial)

    else:
        pv = tools.Prover()
        serialized_instance = pickle.dumps(pv)
        session = uuid4()
        dataSession = SessionData(id=session, prover=serialized_instance)
        session_data = await backend.create(session, dataSession)
        cookie.attach_to_response(response, session)
        r, msg, options = get_options_function(pv,list_index=list_index, 
                                            type_selected=type_selected, 
                                            pb_index=pb_index, sel_rule=sel_rule, 
                                            selected_proof_line_indexes=selected_proof_line_indexes,
                                            total_or_partial=total_or_partial)

    if not r:
        output = SelectedFormOutputDto(
        type_output = "ERROR",
        message = msg,
        lines = [{"content": "", "methods_used_info":"", "type":""}],
    )

        return output
    
    list_options = options_in_rows(options)



    output = SelectedFormOutputDto(
            type_output = "CREATED",
            message = msg,
            lines = list_options,
    )

    return output

    
    







@selected_form_router.post("/selected_form/")
async def selected_form(data: DataInputSelectedFormDto) -> DataOutputSelectedFormDto:
    rows = data.rows
    selected_row_index = data.selected_row_index
    index_option = data.index_option
    selected_rule_index = data.selected_rule_index

    print(rows)
    print(selected_row_index)
    print(index_option)
    print(selected_rule_index)

    #write here

    output = DataOutputSelectedFormDto(
        type_output = "CREATED",
        message="New line created",
        new_line = {"content": "p", "methods_used_info":"4-EQ", "type":"default",}
    )

    return output

