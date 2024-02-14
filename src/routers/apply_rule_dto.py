from typing import Any, Dict, List
from pydantic import BaseModel
from ._shared import NewLine, Rows



class SelectedRuleData(BaseModel):
    type: str
    index_selected_rule: int




class DataInputApplyRuleDto(BaseModel):
    """
    Args:
        rows : This list is a combination of the propositions in the question and the propositions created
    """
    selected_proof_line_indexes: List[int] # this is the index of the selected rows
    pb_index: int
    list_index: int
    type_selected: str
    sel_rule: int 
    input_formula: str = ""
    total_or_partial: str = "total"
    selection: int = 0


class DataOutputApplyRuleDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    type_output: str
    message: str 
    lines: List[NewLine]

