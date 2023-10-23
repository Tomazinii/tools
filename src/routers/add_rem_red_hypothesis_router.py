import select
from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
from .add_rem_red_hypothesis_dto import DataInputAddHypothesisOnlyAddDto, DataInputAddHypothesisRuleDto, DataInputRedAbsDto, DataInputRemoveHypothesisDto, DataOutputAddHypothesisOnlyAddDto, DataOutputAddHypothesisRuleDto, DataOutputRedAbsDto, DataOutputRemoveHypothesisDto

add_rem_red_router = APIRouter()


"""

type for new_line:
    add: are used when we add hypotheses only hypotheses
    rem: are used when we remove hypotheses
    red: are used when we reduce abs
    default: are used when we apply the other rules
    
"""



@add_rem_red_router.post("/add_hypothesis_only_add/")
async def add_hypothesis_only_add(data: DataInputAddHypothesisOnlyAddDto) -> DataOutputAddHypothesisOnlyAddDto:
    selected_rule_index = data.selected_rule_index
    input_data = data.input_data

    print(selected_rule_index)
    print(input_data)



    output = DataOutputAddHypothesisOnlyAddDto(
        type_output = "CREATED",
        message="New line created",
        new_line = {"content": "p -> q", "methods_used_info":"1-ADD", "type":"add",}
    )
    return output



@add_rem_red_router.post("/add_hypothesis_rule/") #ERRO CONCEITUAL: ESSA FUNÇÃO NAO ADICIONA HIPÓTESE.
async def add_hypothesis_rule(data: DataInputAddHypothesisRuleDto) -> DataOutputAddHypothesisRuleDto:
    rows = data.rows
    index_selected_row = data.index_selected_row
    selected_rule_index = data.selected_rule_index # could be 4 or 5
    input_data = data.input_data

    print(rows)
    print(index_selected_row)
    print(selected_rule_index)
    print(input_data)

    #write here

    output = DataOutputAddHypothesisRuleDto(
        type_output = "CREATED",
        message="New line created",
        new_line = {"content": "p -> q", "methods_used_info":"1-ADD", "type":"default",}
    )
    return output



@add_rem_red_router.post("/rem_hypothesis/")
async def rem_hypothesis(data: DataInputRemoveHypothesisDto) -> DataOutputRemoveHypothesisDto:
    rows = data.rows_created

    print(rows)

    #write here

    output = DataOutputRemoveHypothesisDto(
    type_output = "CREATED",
    message="New line created",
    rows_created_modified = [
       {"content": "p", "methods_used_info":"1-ADD", "type":"default",},
       {"content": "q", "methods_used_info":"1-ADD", "type":"rem",},
       {"content": "w", "methods_used_info":"1-ADD", "type":"rem",},
       {"content": "z", "methods_used_info":"1-ADD", "type":"rem",},
        ],
    new_line = {"content": "p -> q", "methods_used_info":"1-ADD", "type":"default"}
    ) 
    return output


@add_rem_red_router.post("/red_absurde/")
async def red_absurde(data: DataInputRedAbsDto) -> DataOutputRedAbsDto:
    rows = data.rows_created
    
    print(rows)

    #write here

    #exemple output
    output = DataOutputRedAbsDto(
    type_output = "CREATED",
    message="New line created",
    rows_created_modified = [
       {"content": "q", "methods_used_info":"1-ADD", "type":"default",},
       {"content": "reduce", "methods_used_info":"1-ADD", "type":"red",},
       {"content": "reduce", "methods_used_info":"1-ADD", "type":"red",},
       {"content": "z", "methods_used_info":"1-ADD", "type":"red",},
        ],
    new_line = {"content": "p -> q", "methods_used_info":"1-ADD", "type":"default"}
    )  

    return output