from dataclasses import dataclass, field
from typing import Union, List, Optional, Tuple


@dataclass
class Parameter:
    def __init__(self, name = None, type = None, is_ptr = False, ptr_depth = 0, is_struct = False,array_length = -1,is_recursive = False):
        self.name = name
        self.type = type
        self.is_ptr = is_ptr
        self.ptr_depth = ptr_depth
        self.is_struct = is_struct
        self.array_length = array_length
        self.is_recursive = is_recursive
    name: str
    type: Union[str, 'StructInfo']  # 参数Type可以是字符串或StructInfo
    is_ptr: bool
    ptr_depth:int
    is_struct: bool
    array_length: int
    is_recursive: bool

@dataclass
class StructInfo:
    def __init__(self, type, parameters_list,is_recursive = False):
        self.type = type
        self.parameter_list = parameters_list
        self.is_recursive = is_recursive
    type: str
    parameter_list: List[Parameter]  # 结构体的参数列表
    is_recursive: bool

@dataclass
class TypeInfo:
    def __init__(self, name, file_path, content_range, code, included_types=None):
        self.name = name
        self.file_path = file_path
        self.content_range = content_range
        self.code = code
        self.alias_set = set()
        self.included_types = included_types if included_types else set()
    name: str
    code: str
    included_types: set[str]  # 该Type依赖的其他Type



@dataclass
class FunctionInfo:
    def __init__(self, file_path = None, name = None, code = None, callee_set = None, func_type = None):
        self.file_path = file_path
        self.name = name
        self.code = code
        self.callee_set = callee_set if callee_set else set()
        self.func_type = func_type
        self.parameter_list = []
        self.annotation = str()
        self.specification = str()
        self.require = str()
        self.include = str()
        
    file_path: str
    name: str
    code: str
    callee_set: set[str]
    func_type: str
    parameter_list: Optional[List[Parameter]]
    annotation: str
    specification: str
    require: str
    include: str

def UNKNOWN_FUNCTION(func_name):
    return FunctionInfo(
    file_path="unknown",
    name=func_name,
    code="",
    callee_set=set(),
    func_type="unknown"
)


@dataclass
class DefInfo:
    typedef_list: List[str]
    define_list: dict[str:str]
