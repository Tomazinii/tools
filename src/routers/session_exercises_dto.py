from typing import Any, Dict, List
from pydantic import BaseModel
from ._shared import Rows


class CreateSessionExerciseDtoInput(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    pb_index: int 
    list_index: int


class CreateSessionExerciseDtoOutput(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    data: Dict[List[Rows], str]