from typing import Any, Dict, List
from pydantic import BaseModel
from ._shared import NewLine, Rows


class DataInputGetOptionsSelectedFormDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """

    rows: List[Rows]
    selected_row_index: int


class DataOutputGetOutputSelectedFormDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    options: List[Rows]


class DataInputSelectedFormDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """
    rows: List[Rows]
    selected_row_index: int
    index_option: int
    selected_rule_index: int # assuming that it is equivalent


class DataOutputSelectedFormDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    type_output: str
    message: str 
    new_line: NewLine




