from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
# from .apply_rule_dto import DataInputApplyRuleDto, DataOutputApplyRuleDto
from exercises import listas_exercises
exercise_api_route = APIRouter()

@exercise_api_route.get("/exercise/")
async def exercise_function():

    return listas_exercises

