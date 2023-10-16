from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
from .apply_rule_dto import DataInputApplyRuleDto, DataOutputApplyRuleDto

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


@apply_rule_router.post("/apply_rule_router/")
async def apply_rule(data: DataInputApplyRuleDto) -> DataOutputApplyRuleDto:

    #write here

    output = DataOutputApplyRuleDto(
        type_output = "ERROR",
        message="Invalid rows to apply rule",
        new_line = {"content": "", "methods_used_info":"", "type":"",}
    )


    return output

