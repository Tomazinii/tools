from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
# from .apply_rule_dto import DataInputApplyRuleDto, DataOutputApplyRuleDto

exercise_api_route = APIRouter()

@exercise_api_route.get("/exercise/")
async def exercise_function():

    question = "1 - ~~p → q ⊢ p -> q" 

    return question

