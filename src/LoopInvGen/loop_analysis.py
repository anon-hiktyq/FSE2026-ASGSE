import json
import re
import openai
import logging
class LoopAnalysis:
    def __init__(self,json_file,idx,logger:logging.Logger):
        """
        :param json_file: JSON 文件路径或数据
        :param idx: 需要提取的循环索引
        """
        self.logger = logger
        self.json_file = json_file
        self.idx = idx
        self.pre_condition =None
        self.path_conds = None
        self.loop_condition = None
        self.updated_loop_conditions = None
        self.var_maps = None
        self.array_names = None
        self.unchanged_arrays = None
        self.global_unchanged_vars = None
        self.non_inductive_vars = None
        

    def get_json_at_index(self):
        with open(self.json_file, 'r') as file:
            data = json.load(file)  # 读取并解析 JSON 文件
            
            if isinstance(data, list) and 0 <= self.idx < len(data):
                return data[self.idx]  # 返回第 idx 个 JSON 对象
            else:
                raise IndexError("Index out of range or data is not a list")
            
    

    def extract_precond_from_file(self):
        
        loop = self.get_json_at_index()  
        condition = loop.get("condition", "")  
        return condition


    
    def extract_unchanged_vars(self):
        
        loop = self.get_json_at_index()  
        loop_content = loop.get("content", "")  
        var_map = self.var_maps[0] 

        unchanged_vars = []

        for var_name in var_map.keys():
      
            escaped_var = re.escape(var_name)
            pattern = re.compile(
                rf"(\b{escaped_var}\b\s*(\+\+|--|\+=|-=|\*=|/=|=(?!=))|(\+\+|--)\s*\b{escaped_var}\b)"
            )
            if not pattern.search(loop_content):
                unchanged_vars.append(var_name)

        return unchanged_vars
    
    
    
    def extract_non_inductive_vars(self):
        loop = self.get_json_at_index()
        loop_content = loop.get("content", "")
        var_map = self.var_maps[0]
        var_names = set(var_map.keys())

        results = []
        lines = loop_content.split('\n')
        for idx, line in enumerate(lines, 1):
            for var in var_names:
               
                m = re.match(rf"\s*{re.escape(var)}\s*=(?!=)", line)
                if m:
                    # 取等号右侧
                    right_side = line.split('=', 1)[1]
                    # 检查右侧是否用到自己
                    if not re.search(rf"\b{re.escape(var)}\b", right_side):
                        results.append(var)
        return results


    def extract_array_names(self):
        array_names = set()  # 使用集合避免重复
        
        # 从循环内容中提取数组
        loop = self.get_json_at_index()
        loop_content = loop.get("content", "")
        if loop_content:
            array_names.update(self._extract_from_loop_content(loop_content))
        
        return list(array_names)
    
    def _extract_from_precondition(self):
        array_names = []
        pre_condition = self.pre_condition
        start = 0
        length = len(pre_condition)
        
        while start < length:
            # 查找 'store_int_array' 的位置
            func_idx = pre_condition.find('store_int_array', start)
            if func_idx == -1:
                break  # 没有更多函数调用
            
            # 查找左括号的位置
            left_paren = pre_condition.find('(', func_idx)
            if left_paren == -1:
                start = func_idx + 1
                continue
            
            # 查找右括号的位置
            right_paren = pre_condition.find(')', left_paren)
            if right_paren == -1:
                start = func_idx + 1
                continue
            
            # 提取参数部分并分割
            param_str = pre_condition[left_paren+1:right_paren].strip()
            params = [p.strip() for p in param_str.split(',')]
            
            if len(params) >= 3:
                third_param = params[2]
                # 去除末尾的 '_l'
                if third_param.endswith('_l'):
                    third_param = third_param[:-2]
                array_names.append(third_param)
            
            # 继续查找下一个函数调用
            start = right_paren + 1
        
        return array_names
    
    def _extract_from_loop_content(self, loop_content):
        """从循环内容中提取所有数组名"""
        array_names = []
        
        # 1. 匹配数组声明Mode
        array_decl_patterns = [
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s+(?:\*?\s*)(\w+)\s*\[',  # int arr[10], int* arr[10]
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b',  # int* arr
            r'\b(\w+)\s*\[[^\]]*\]\s*='  # arr[10] = ...
        ]
        
        for pattern in array_decl_patterns:
            matches = re.findall(pattern, loop_content)
            array_names.extend(matches)
        
        # 2. 匹配数组使用Mode：arr[i], arr[0], arr[n]（排除已经被 p->a Mode匹配的）
        # 先收集所有 p->a Mode的数组名
        ptr_array_pattern = r'(\w+\s*->\s*\w+)\s*\[[^\]]*\]'  # p->a[i] 提取 p->a
        ptr_arrays = re.findall(ptr_array_pattern, loop_content)
        array_names.extend(ptr_arrays)
        
        # 收集所有结构体数组成员
        struct_array_pattern = r'(\w+\.\w+)\s*\[[^\]]*\]'  # struct.arr[i] 提取 struct.arr
        struct_arrays = re.findall(struct_array_pattern, loop_content)
        array_names.extend(struct_arrays)
        
        # 3. 匹配函数参数中的数组声明
        param_array_patterns = [
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s+(\w+)\s*\[\s*\]',  # int arr[]
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b',     # int* arr
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b'      # int* arr[]
        ]
        
        for pattern in param_array_patterns:
            matches = re.findall(pattern, loop_content)
            array_names.extend(matches)
        
        # 4. 匹配简单的数组使用Mode，但排除已经被 p->a 或 struct.arr Mode匹配的
        simple_array_pattern = r'\b(\w+)\s*\[[^\]]*\]'
        simple_arrays = re.findall(simple_array_pattern, loop_content)
        
        # 过滤掉已经被复合Mode匹配的数组名
        for simple_array in simple_arrays:
            # 检查这个简单数组名是否已经包含在复合Mode中
            is_contained = False
            for ptr_array in ptr_arrays:
                if simple_array in ptr_array:
                    is_contained = True
                    break
            for struct_array in struct_arrays:
                if simple_array in struct_array:
                    is_contained = True
                    break
            
            # 如果没有被包含，则添加
            if not is_contained:
                array_names.append(simple_array)
        
        return array_names
    
    def _extract_from_function_signature(self):
        """从函数签名中提取数组参数"""
        array_names = []
        
        # 获取函数内容
        loop = self.get_json_at_index()
        if not loop:
            return array_names
        
        # 查找函数定义
        function_patterns = [
            r'void\s+(\w+)\s*\([^)]*\)',  # void func(...)
            r'int\s+(\w+)\s*\([^)]*\)',   # int func(...)
            r'(\w+)\s+(\w+)\s*\([^)]*\)'  # type func(...)
        ]
        
        # 这里可以扩展来解析函数参数中的数组声明
        # 暂时返回空列表，可以根据需要扩展
        
        return array_names


    def extract_unchanged_arrays(self):
        """
        提取没有被写入只读取的数组名
        返回一个列表，包含所有只读的数组名
        """
        if not self.array_names:
            return []
        
        loop = self.get_json_at_index()
        loop_content = loop.get("content", "")
        
        unchanged_arrays = []
        
        for array_name in self.array_names:
            
            
            escaped_array = re.escape(array_name)
            
            # 构建写入Mode的正则表达式
            write_patterns = [
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*=",  # array[index] =
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*\+=",  # array[index] +=
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*-=",  # array[index] -=
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*\*=",  # array[index] *=
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*/=",  # array[index] /=
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*\+\+",  # array[index]++
                rf"\b{escaped_array}\s*\[\s*\w+\s*\]\s*--",  # array[index]--
                rf"\+\+\s*{escaped_array}\s*\[\s*\w+\s*\]",  # ++array[index]
                rf"--\s*{escaped_array}\s*\[\s*\w+\s*\]",  # --array[index]
            ]
            
            # 检查是否有任何写入Mode匹配
            is_written = False
            for pattern in write_patterns:
                if re.search(pattern, loop_content):
                    is_written = True
                    break
            
            # 如果没有Found写入Mode，说明数组是只读的
            if not is_written:
                unchanged_arrays.append(array_name)
        
        return unchanged_arrays


    def extract_var_map_from_file(self):
        loop = self.get_json_at_index() 
        condition = loop.get("condition", "") 
        print(condition)

        sub_conditions = [s.strip() for s in condition.split("||")]

        var_maps = []
        path_conds = []

        def split_path_and_state(expression):
            """
            按最后一个 && 分割字符串，得到 path 和 state
            :param expression: Input的表达式字符串
            :return: 返回 path 和 state 两部分
            """
            # 查找最后一个 && 的位置
            last_and_index = expression.rfind("&&")

            if last_and_index == -1:
                # 如果没有Found &&，path 为空，整个表达式作为 state
                path = None
                state = expression.strip()
            else:
                # 按最后一个 && 分割
                path = expression[:last_and_index].strip()
                path_parts = path.split('&&')
                valid_parts = []
                for part in path_parts:
                    if 'exists' in path_parts or 'forall' in path_parts:
                        continue
                    else:
                        valid_parts.append(part)

                if path_parts == []:
                    path =None
                else:
                    path = '&&'.join(valid_parts)

                state = expression[last_and_index + 2:].strip()

            return path, state

        # 正则表达式匹配形如 "var == value" 的部分，支持嵌套括号


        def parse_expressions(s):
            var_map = {}
            remaining = s.strip()
            stack = []
            expr_start = 0
            i = 0
            n = len(remaining)
            
            while i < n:
                char = remaining[i]
                
                # 处理括号层级
                if char == '(':
                    stack.append(i)
                elif char == ')':
                    if stack:
                        stack.pop()
                
                # 遇到逻辑运算符且不在括号内时，分割表达式
                if i < n-1 and remaining[i:i+2] in ('&&', '* ') and not stack:
                    # 提取当前表达式
                    expr = remaining[expr_start:i].strip()
                    # 解析表达式中的键值对
                    eq_pos = expr.find('==')
                    if eq_pos != -1:
                        var = expr[:eq_pos].strip(' ()')
                        value = expr[eq_pos+2:].strip(' ()')
                        var_map[var] = value
                    expr_start = i + 2
                    i += 1  # Skip运算符的第二个字符
                
                i += 1
            
            # 处理最后一个表达式
            expr = remaining[expr_start:].strip()
            eq_pos = expr.find('==')
            if eq_pos != -1:
                var = expr[:eq_pos].strip(' ()')
                value = expr[eq_pos+2:].strip(' ()')
                var_map[var] = value
                
            return var_map

        for sub_condition in sub_conditions:

            path,state = split_path_and_state(sub_condition)
            var_map = {}  # 为每个子条件创建一个新的 var_map
            path_cond = path
            path_conds.append(path_cond)
           
            var_map = parse_expressions(state)
            var_maps.append(var_map)  # 将 var_map 添加到列表中


        variables_to_exclude = set()
        for var_key in var_maps[0].keys():
            variables_to_exclude.add(f'{var_key}_v')
            variables_to_exclude.add(f'{var_key}_length')

        new_path_conds = []

        # print(variables_to_exclude)

        for p in path_conds:
            if p is None:
                new_path_conds.append(None)
                continue
            
            parts = p.split('&&')
            filtered_parts = [part.strip() for part in parts if not any(exclude_var in part for exclude_var in variables_to_exclude)]
            path_cond = ' && '.join(filtered_parts) or None
            new_path_conds.append(path_cond)

        variables_to_replace = set()
        for var_key in var_maps[0].keys():
            variables_to_replace.add(f'{var_key}_l')
        
        for replacement in variables_to_replace:
            for path_cond in new_path_conds:
                if path_cond:
                    # 只替换变量名末尾的 _l，不替换中间的 _l
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    path_cond = re.sub(pattern, replacement[:-2], path_cond)
            
            for var_map in var_maps:
                for key in var_map.keys():
                    # 只替换变量名末尾的 _l，不替换中间的 _l
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    var_map[key] = re.sub(pattern, replacement[:-2], var_map[key])
                    
        path_conds = new_path_conds
        # path_conds = [' && '.join([part.strip() for part in p.split('&&') if '{var_maps[0][keys]}_v' not in part]) or None for p in path_conds]

        return var_maps,path_conds
    
    def extract_first_loop_condition(self):
       
        loop = self.get_json_at_index()
        code = loop.get("content", "")
        
        # 查找第一个出现的 for 或 while 关键字
        loop_keywords = ["for", "while"]
        first_pos = len(code)
        keyword_found = None
        for keyword in loop_keywords:
            pos = code.find(keyword)
            if pos != -1 and pos < first_pos:
                first_pos = pos
                keyword_found = keyword
        if keyword_found is None:
            return None  # 未Found循环关键字
        
        # 确保Found的是完整的关键字
        if (first_pos > 0 and (code[first_pos-1].isalnum() or code[first_pos-1]=='_')) or \
        (first_pos + len(keyword_found) < len(code) and (code[first_pos+len(keyword_found)].isalnum() or code[first_pos+len(keyword_found)]=='_')):
            return None
        
        # 定位 '('（Skip关键字和空格）
        cursor = first_pos + len(keyword_found)
        while cursor < len(code) and code[cursor].isspace():
            cursor += 1
        if cursor >= len(code) or code[cursor] != '(':
            return None  # 没有Found左括号
        cursor += 1  # Skip '('
        
        # 提取括号内的内容，支持括号嵌套
        condition_start = cursor
        paren_depth = 1
        while cursor < len(code) and paren_depth > 0:
            if code[cursor] == '(':
                paren_depth += 1
            elif code[cursor] == ')':
                paren_depth -= 1
            cursor += 1
        if paren_depth != 0:
            return None  # 括号不匹配
        inner = code[condition_start: cursor-1].strip()
        
        # 提取条件
        condition = None
        if keyword_found == "while":
            # while 循环条件为整个括号内内容
            condition = inner
        elif keyword_found == "for":
            # for 循环通常包含三个表达式：初始化; 条件; 迭代，条件在中间
            parts = []
            part = ""
            nested = 0  # 处理内部括号嵌套
            for ch in inner:
                if ch == '(':
                    nested += 1
                elif ch == ')':
                    nested -= 1
                if ch == ';' and nested == 0:
                    parts.append(part.strip())
                    part = ""
                else:
                    part += ch
            parts.append(part.strip())
            # 条件部分位于第二个分号分隔部分（若存在）
            if len(parts) >= 2:
                condition = parts[1]
            else:
                condition = None

            if condition == '':
                condition = None
        return condition

    


    def replace_vars_with_values(self, loop_cond, var_maps):
        
        updated_loop_conditions = []

        if loop_cond == None:
            return [None]

        for var_map in var_maps:
            # 将字符串转换为列表，方便修改
            loop_cond_list = list(loop_cond)
            i = 0  # 当前查找位置

            while i < len(loop_cond_list):
                # 从左到右查找变量名
                for var in var_map:
                    # 检查当前位置是否匹配变量名
                    if loop_cond_list[i:i + len(var)] == list(var):
                        # 检查变量名是否完整（前后是单词边界或非字母数字字符）
                        is_start_boundary = (i == 0 or not loop_cond_list[i - 1].isalnum())
                        is_end_boundary = (i + len(var) >= len(loop_cond_list) or not loop_cond_list[i + len(var)].isalnum())
                        if is_start_boundary and is_end_boundary:
                            # 替换变量名
                            loop_cond_list[i:i + len(var)] = list(var_map[var])
                            # Skip替换后的部分
                            i += len(var_map[var]) - 1
                            break
                i += 1

            # 将列表转换回字符串并添加到Result中
            updated_loop_conditions.append(''.join(loop_cond_list))

        return updated_loop_conditions
    



    def run(self):

        

        # 提取变量映射
        var_maps,path_conds = self.extract_var_map_from_file()
        self.var_maps =var_maps
        self.path_conds = path_conds
        self.logger.info(f"Variable Maps:{var_maps}")
        self.logger.info(f"Path conditions: {path_conds}")
    

        # 提取前置条件
        pre_condition = self.extract_precond_from_file()
        self.pre_condition =pre_condition
        self.logger.info(f"Pre condition: {pre_condition}")

        # 提取循环条件
        loop_condition = self.extract_first_loop_condition()
        self.loop_condition = loop_condition
        self.logger.info(f"Loop Condition: {loop_condition}")

        # 提取 array 变量名
        array_names = self.extract_array_names()
        self.array_names = array_names
        self.logger.info(f"Array Names: {array_names}")

        # 替换循环条件中的变量为值
        if var_maps :
            updated_loop_conditions = self.replace_vars_with_values(loop_condition, var_maps)
            self.updated_loop_conditions = updated_loop_conditions
            self.logger.info(f"Updated Loop Conditions: {updated_loop_conditions}")

        global_unchanged_vars  = self.extract_unchanged_vars()
        self.global_unchanged_vars = global_unchanged_vars 
        self.logger.info(f"Global Unchanged Variables: {global_unchanged_vars}")

        non_inductive_vars = self.extract_non_inductive_vars()
        self.non_inductive_vars = non_inductive_vars
        self.logger.info(f"Non Inductive Variables: {non_inductive_vars}")

        # 提取只读数组
        unchanged_arrays = self.extract_unchanged_arrays()
        self.unchanged_arrays = unchanged_arrays
        self.logger.info(f"Unchanged Arrays (Read-only): {unchanged_arrays}")










# 示例调用 
if __name__ == "__main__":
   
   json_file = 'loop/09.json'
   idx = 0
   analyzer= LoopAnalysis(json_file,idx)
   analyzer.run()