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
    rows: List[Rows] # This list is a combination of the propositions in the question and the propositions created
    index_selected_rows: List[int] # this is the index of the selected rows
    selected_rule_data: SelectedRuleData # This dictionary contains the data 


class DataOutputApplyRuleDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    type_output: str
    message: str 
    new_line: NewLine

