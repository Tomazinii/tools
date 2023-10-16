from pydantic import BaseModel


class NewLine(BaseModel):
    content: str
    methods_used_info: str
    type: str = "default"

class Rows(BaseModel):
    content: str
    type: str = "default"
    methods_used_info: str

