from typing import Any, Dict, List
from pydantic import BaseModel
from ._shared import NewLine, Rows


class DataInputGetOptionsSelectedFormDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """

    selected_proof_line_indexes: List[int]
    pb_index: int
    list_index: int
    type_selected: str
    sel_rule: int
    total_or_partial:str



class DataOutputGetOutputSelectedFormDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    data: Any


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





class SelectedFormOutputDto(BaseModel):
    type_output: str
    message: str 
    lines: List[Rows]