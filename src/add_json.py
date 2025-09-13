import json
from config import LLMConfig
from llm import *


api_config = LLMConfig()
llm = Chatbot(api_config)


# 1. 原始 JSON 字符串
json_string = '''{   
        "name": "none",
        "category": "none",
        "type": "none",
        "input": "none",
        "output": "none",
        "value": "none",
        "explanation": "none"
    }'''

# 2. 将字符串解析为 Python 字典
data = json.loads(json_string)

# 3. (可选) 修改数据
data['name'] = "list_append"
data['category'] = 'loop invariant'
data['type'] = 'list'
data['input'] = '''
#include <stdlib.h>

struct list {
  struct list *tail;
};

/*@
PLACE_HOLDER_PREDICATE_OR_LOGIC_FUNCTION
*/

/*@
requires PLACE_HOLDER;
ensures PLACE_HOLDER;
*/
struct list * append(struct list *x, struct list *y) {
  struct list *t, *u;

  if (x == NULL) {
    return y;
  } else {
    t = x;
    u = t->tail;

    /*>>> LOOP INVARIANT TO FILL <<< */

    /*@
      PLACE_HOLDER_LOOP         
    */
    while (u != NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}
'''
data['output'] = '''
#include <stdlib.h>

struct list {
  struct list *tail;
};

/*@
  predicate lseg{L}(struct list* x, struct list* y) =
    x == y || (x != y && \\valid(x) && \separated(x, y) && lseg{L}(x->tail, y));
*/

/*@
  predicate listrep(struct list* head) = lseg(head, NULL);
*/

/*@
predicate disjoint(struct list* x, struct list* y) =
    \separated(x, y) &&
    \\forall struct list* p, struct list* q;
      lseg(x,p) && lseg(y,q) ==> \separated(p,q);
*/

/*@
  requires listrep(x) && listrep(y);
  requires disjoint(x, y);
  ensures listrep(\\result);
*/
struct list * append(struct list *x, struct list *y) {
  struct list *t, *u;

  if (x == NULL) {
    return y;
  } else {
    t = x;
    u = t->tail;

    /*@
      loop invariant u == t->tail;
      loop invariant listrep(t);          
      loop invariant listrep(u);            
      loop invariant listrep(y);     
      loop invariant lseg(x, t);           
    */
    while (u != NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

'''
code = data['input']
data['value'] = llm.chat(f'Please brief explain what the following code do: {code}')
code = data['output']
data['explanation'] = llm.chat(f'Please brief explain why the specifications (preconditions, postconditions and loop invariants) are correct: {code}')

# 4. 将字典写入文件
class Json:
    def __init__(self,json_data):

        self.json_data = json_data

    def addJson(self,file_path):

        try:
            # 2. 读取现有文件
            with open(file_path, 'r', encoding='utf-8') as f:
                # 解析文件内容为 Python 列表
                existing_data = json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            # 如果文件不存在或为空，则创建一个新的空列表
            existing_data = []

        # 3. 将新对象追加到列表中
        existing_data.append(self.json_data)

        # 4. 将整个列表写回文件
        with open(file_path, 'w', encoding='utf-8') as f:
            # 使用 json.dump() 写入文件，设置 indent 参数让文件更易读
            json.dump(existing_data, f, indent=4, ensure_ascii=False)

        print(f"新数据已成功追加到 {file_path}")

if __name__ == "__main__":
    
    json_obj = Json(data)
    json_obj.addJson('./VectorDB/Jsons/init.json')