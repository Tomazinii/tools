from typing import Any, Dict, List
from pydantic import BaseModel
from ._shared import NewLine,Rows


"""

type for new_line:
    add: are used when we add hypotheses only hypotheses
    rem: are used when we remove hypotheses
    red: are used when we reduce abs
    default: are used when we apply the other rules
"""


class DataInputAddHypothesisOnlyAddDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """
    selected_rule_index: int = 0
    input_data: List[str]


class DataOutputAddHypothesisOnlyAddDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    type_output: str
    message: str
    new_line: NewLine
    
    



class DataInputAddHypothesisRuleDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """
    rows: List[Rows] # This list is a combination of the propositions in the question and the propositions created
    index_selected_row: int 
    selected_rule_index: int # could be 4 or 5
    input_data: List[str]


class DataOutputAddHypothesisRuleDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    type_output: str
    message: str
    new_line: NewLine



class DataInputRemoveHypothesisDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """
    rows_created: List[Rows] # This list is a combination of the propositions in the question and the propositions created


class DataOutputRemoveHypothesisDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    rows_created_modified: List[Rows]
    new_line: NewLine
    type_output: str
    message: str




class DataInputRedAbsDto(BaseModel):
    """
        Type of data input.
        all mandatory 
    """
    rows_created: List[Rows]  # This list is a combination of the propositions in the question and the propositions created


class DataOutputRedAbsDto(BaseModel):
    """
        Type of data outPut.
        all mandatory 
    """
    rows_created_modified: List[Rows]
    new_line: NewLine
    type_output: str
    message: str

