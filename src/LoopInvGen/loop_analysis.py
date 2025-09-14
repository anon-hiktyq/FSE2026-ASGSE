import json
import re
import openai
import logging
class LoopAnalysis:
    def __init__(self,json_file,idx,logger:logging.Logger):
        """
        :param json_file: JSON file path or data
        :param idx: Loop index to extract
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
            data = json.load(file)  # Read and parse JSON file
            
            if isinstance(data, list) and 0 <= self.idx < len(data):
                return data[self.idx]  # Return the idx-th JSON object
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
                    # Get the right side of the equals sign
                    right_side = line.split('=', 1)[1]
                    # Check if the right side uses itself
                    if not re.search(rf"\b{re.escape(var)}\b", right_side):
                        results.append(var)
        return results


    def extract_array_names(self):
        array_names = set()  # Use set to avoid duplicates
        
        # Extract arrays from loop content
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
            # Find position of 'store_int_array'
            func_idx = pre_condition.find('store_int_array', start)
            if func_idx == -1:
                break  # No more function calls
            
            # Find position of left parenthesis
            left_paren = pre_condition.find('(', func_idx)
            if left_paren == -1:
                start = func_idx + 1
                continue
            
            # Find position of right parenthesis
            right_paren = pre_condition.find(')', left_paren)
            if right_paren == -1:
                start = func_idx + 1
                continue
            
            # Extract parameter part and split
            param_str = pre_condition[left_paren+1:right_paren].strip()
            params = [p.strip() for p in param_str.split(',')]
            
            if len(params) >= 3:
                third_param = params[2]
                # Remove trailing '_l'
                if third_param.endswith('_l'):
                    third_param = third_param[:-2]
                array_names.append(third_param)
            
            # Continue searching for next function call
            start = right_paren + 1
        
        return array_names
    
    def _extract_from_loop_content(self, loop_content):
        """Extract all array names from loop content"""
        array_names = []
        
        # 1. Match array declaration patterns
        array_decl_patterns = [
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s+(?:\*?\s*)(\w+)\s*\[',  # int arr[10], int* arr[10]
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b',  # int* arr
            r'\b(\w+)\s*\[[^\]]*\]\s*='  # arr[10] = ...
        ]
        
        for pattern in array_decl_patterns:
            matches = re.findall(pattern, loop_content)
            array_names.extend(matches)
        
        # 2. Match array usage patterns: arr[i], arr[0], arr[n] (exclude those already matched by p->a patterns)
        # First collect all p->a pattern array names
        ptr_array_pattern = r'(\w+\s*->\s*\w+)\s*\[[^\]]*\]'  # p->a[i] extract p->a
        ptr_arrays = re.findall(ptr_array_pattern, loop_content)
        array_names.extend(ptr_arrays)
        
        # Collect all struct array members
        struct_array_pattern = r'(\w+\.\w+)\s*\[[^\]]*\]'  # struct.arr[i] extract struct.arr
        struct_arrays = re.findall(struct_array_pattern, loop_content)
        array_names.extend(struct_arrays)
        
        # 3. Match array declarations in function parameters
        param_array_patterns = [
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s+(\w+)\s*\[\s*\]',  # int arr[]
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b',     # int* arr
            r'\b(?:int|char|float|double|long|short|unsigned|signed)\s*\*\s*(\w+)\b'      # int* arr[]
        ]
        
        for pattern in param_array_patterns:
            matches = re.findall(pattern, loop_content)
            array_names.extend(matches)
        
        # 4. Match simple array usage patterns, but exclude those already matched by p->a or struct.arr patterns
        simple_array_pattern = r'\b(\w+)\s*\[[^\]]*\]'
        simple_arrays = re.findall(simple_array_pattern, loop_content)
        
        # Filter out array names already matched by composite patterns
        for simple_array in simple_arrays:
            # Check if this simple array name is already contained in composite patterns
            is_contained = False
            for ptr_array in ptr_arrays:
                if simple_array in ptr_array:
                    is_contained = True
                    break
            for struct_array in struct_arrays:
                if simple_array in struct_array:
                    is_contained = True
                    break
            
            # If not contained, add it
            if not is_contained:
                array_names.append(simple_array)
        
        return array_names
    
    def _extract_from_function_signature(self):
        """Extract array parameters from function signature"""
        array_names = []
        
        # Get function content
        loop = self.get_json_at_index()
        if not loop:
            return array_names
        
        # Find function definitions
        function_patterns = [
            r'void\s+(\w+)\s*\([^)]*\)',  # void func(...)
            r'int\s+(\w+)\s*\([^)]*\)',   # int func(...)
            r'(\w+)\s+(\w+)\s*\([^)]*\)'  # type func(...)
        ]
        
        
        return array_names


    def extract_unchanged_arrays(self):
        """
        Extract array names that are not written to but only read
        Returns a list containing all read-only array names
        """
        if not self.array_names:
            return []
        
        loop = self.get_json_at_index()
        loop_content = loop.get("content", "")
        
        unchanged_arrays = []
        
        for array_name in self.array_names:
            
            
            escaped_array = re.escape(array_name)
            
            # Build write pattern regular expressions
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
            
            # Check if any write pattern matches
            is_written = False
            for pattern in write_patterns:
                if re.search(pattern, loop_content):
                    is_written = True
                    break
            
            # If no write pattern found, the array is read-only
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
            Split string by the last && to get path and state
            :param expression: Input expression string
            :return: Return path and state parts
            """
            # Find position of last &&
            last_and_index = expression.rfind("&&")

            if last_and_index == -1:
                # If no && found, path is empty, entire expression as state
                path = None
                state = expression.strip()
            else:
                # Split by last &&
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

        # Regular expression matching patterns like "var == value", supporting nested parentheses


        def parse_expressions(s):
            var_map = {}
            remaining = s.strip()
            stack = []
            expr_start = 0
            i = 0
            n = len(remaining)
            
            while i < n:
                char = remaining[i]
                
                # Handle parenthesis nesting
                if char == '(':
                    stack.append(i)
                elif char == ')':
                    if stack:
                        stack.pop()
                
                # When encountering logical operators and not inside parentheses, split expression
                if i < n-1 and remaining[i:i+2] in ('&&', '* ') and not stack:
                    # Extract current expression
                    expr = remaining[expr_start:i].strip()
                    # Parse key-value pairs in expression
                    eq_pos = expr.find('==')
                    if eq_pos != -1:
                        var = expr[:eq_pos].strip(' ()')
                        value = expr[eq_pos+2:].strip(' ()')
                        var_map[var] = value
                    expr_start = i + 2
                    i += 1  # Skip second character of operator
                
                i += 1
            
            # Process last expression
            expr = remaining[expr_start:].strip()
            eq_pos = expr.find('==')
            if eq_pos != -1:
                var = expr[:eq_pos].strip(' ()')
                value = expr[eq_pos+2:].strip(' ()')
                var_map[var] = value
                
            return var_map

        for sub_condition in sub_conditions:

            path,state = split_path_and_state(sub_condition)
            var_map = {}  # Create a new var_map for each sub-condition
            path_cond = path
            path_conds.append(path_cond)
           
            var_map = parse_expressions(state)
            var_maps.append(var_map)  # Add var_map to list


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
                    # Only replace _l at the end of variable names, not in the middle
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    path_cond = re.sub(pattern, replacement[:-2], path_cond)
            
            for var_map in var_maps:
                for key in var_map.keys():
                    # Only replace _l at the end of variable names, not in the middle
                    import re
                    pattern = r'\b' + re.escape(replacement) + r'\b'
                    var_map[key] = re.sub(pattern, replacement[:-2], var_map[key])
                    
        path_conds = new_path_conds
        # path_conds = [' && '.join([part.strip() for part in p.split('&&') if '{var_maps[0][keys]}_v' not in part]) or None for p in path_conds]

        return var_maps,path_conds
    
    def extract_first_loop_condition(self):
       
        loop = self.get_json_at_index()
        code = loop.get("content", "")
        
        # Find first occurrence of for or while keyword
        loop_keywords = ["for", "while"]
        first_pos = len(code)
        keyword_found = None
        for keyword in loop_keywords:
            pos = code.find(keyword)
            if pos != -1 and pos < first_pos:
                first_pos = pos
                keyword_found = keyword
        if keyword_found is None:
            return None  # Loop keyword not found
        
        # Ensure found is complete keyword
        if (first_pos > 0 and (code[first_pos-1].isalnum() or code[first_pos-1]=='_')) or \
        (first_pos + len(keyword_found) < len(code) and (code[first_pos+len(keyword_found)].isalnum() or code[first_pos+len(keyword_found)]=='_')):
            return None
        
        # Locate '(' (skip keyword and spaces)
        cursor = first_pos + len(keyword_found)
        while cursor < len(code) and code[cursor].isspace():
            cursor += 1
        if cursor >= len(code) or code[cursor] != '(':
            return None  # Left parenthesis not found
        cursor += 1  # Skip '('
        
        # Extract content inside parentheses, supporting nested parentheses
        condition_start = cursor
        paren_depth = 1
        while cursor < len(code) and paren_depth > 0:
            if code[cursor] == '(':
                paren_depth += 1
            elif code[cursor] == ')':
                paren_depth -= 1
            cursor += 1
        if paren_depth != 0:
            return None  # Parentheses don't match
        inner = code[condition_start: cursor-1].strip()
        
        # Extract condition
        condition = None
        if keyword_found == "while":
            # while loop condition is entire content inside parentheses
            condition = inner
        elif keyword_found == "for":
            # for loop usually contains three expressions: initialization; condition; iteration, condition is in the middle
            parts = []
            part = ""
            nested = 0  # Handle internal parenthesis nesting
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
            # Condition part is in the second semicolon-separated part (if exists)
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
            # Convert string to list for easy modification
            loop_cond_list = list(loop_cond)
            i = 0  # Current search position

            while i < len(loop_cond_list):
                # Search for variable names from left to right
                for var in var_map:
                    # Check if current position matches variable name
                    if loop_cond_list[i:i + len(var)] == list(var):
                        # Check if variable name is complete (word boundaries or non-alphanumeric characters before and after)
                        is_start_boundary = (i == 0 or not loop_cond_list[i - 1].isalnum())
                        is_end_boundary = (i + len(var) >= len(loop_cond_list) or not loop_cond_list[i + len(var)].isalnum())
                        if is_start_boundary and is_end_boundary:
                            # Replace variable name
                            loop_cond_list[i:i + len(var)] = list(var_map[var])
                            # Skip replaced part
                            i += len(var_map[var]) - 1
                            break
                i += 1

            # Convert list back to string and add to result
            updated_loop_conditions.append(''.join(loop_cond_list))

        return updated_loop_conditions
    



    def run(self):

        

        # Extract variable mapping
        var_maps,path_conds = self.extract_var_map_from_file()
        self.var_maps =var_maps
        self.path_conds = path_conds
        self.logger.info(f"Variable Maps:{var_maps}")
        self.logger.info(f"Path conditions: {path_conds}")
    

        # Extract precondition
        pre_condition = self.extract_precond_from_file()
        self.pre_condition =pre_condition
        self.logger.info(f"Pre condition: {pre_condition}")

        # Extract loop condition
        loop_condition = self.extract_first_loop_condition()
        self.loop_condition = loop_condition
        self.logger.info(f"Loop Condition: {loop_condition}")

        # Extract array variable names
        array_names = self.extract_array_names()
        self.array_names = array_names
        self.logger.info(f"Array Names: {array_names}")

        # Replace variables in loop condition with values
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

        # Extract read-only arrays
        unchanged_arrays = self.extract_unchanged_arrays()
        self.unchanged_arrays = unchanged_arrays
        self.logger.info(f"Unchanged Arrays (Read-only): {unchanged_arrays}")










# Example usage 
if __name__ == "__main__":
   
   json_file = 'loop/09.json'
   idx = 0
   analyzer= LoopAnalysis(json_file,idx)
   analyzer.run()