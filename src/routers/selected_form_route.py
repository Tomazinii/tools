from typing import Any, Dict, List
from pydantic import BaseModel
from fastapi import APIRouter
from .selected_form_dto import DataInputGetOptionsSelectedFormDto, DataInputSelectedFormDto, DataOutputGetOutputSelectedFormDto, DataOutputSelectedFormDto

selected_form_router = APIRouter()

@selected_form_router.post("/get_options_selected_form/")
async def get_options_selected_form(data: DataInputGetOptionsSelectedFormDto) -> DataOutputGetOutputSelectedFormDto:

    #write here

    output = DataOutputGetOutputSelectedFormDto(
        options = [
            {"content": "∼∼p → q - AT POS 0", "methods_used_info":"", "type":""},
            {"content": "∼∼p - AT POS 0", "methods_used_info":"", "type":""},
            {"content": "∼p - AT POS 1", "methods_used_info":"", "type":""},
            {"content": "p - AT POS 2", "methods_used_info":"", "type":""},
            {"content": "q - AT POS 6", "methods_used_info":"", "type":""},
            ]
    ) 
    return output


@selected_form_router.post("/selected_form/")
async def selected_form(data: DataInputSelectedFormDto) -> DataOutputSelectedFormDto:

    #write here

    output = DataOutputSelectedFormDto(
        type_output = "CREATED",
        message="New line created",
        new_line = {"content": "p", "methods_used_info":"4-EQ", "type":"default",}
    )

    return output

