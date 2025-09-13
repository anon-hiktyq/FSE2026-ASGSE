import json
import yaml
import os
from typing import Dict, Any, Union,Tuple
from config import CodeAnalyzerConfig, LLMConfig


class ConfigLoader:
    """配置文件加载器，支持 JSON 和 YAML 格式"""
    
    def __init__(self, config_path: str):
        """
        初始化配置加载器
        
        Args:
            config_path (str): 配置文件路径
        """
        self.config_path = config_path
        self.config_data = self._load_config()
    
    def _load_config(self) -> Dict[str, Any]:
        """加载配置文件"""
        if not os.path.exists(self.config_path):
            raise FileNotFoundError(f"配置文件不存在: {self.config_path}")
        
        with open(self.config_path, 'r', encoding='utf-8') as f:
            if self.config_path.endswith('.json'):
                return json.load(f)
            elif self.config_path.endswith(('.yml', '.yaml')):
                return yaml.safe_load(f)
            else:
                raise ValueError(f"不支持的配置文件格式: {self.config_path}")
    
    def get_code_analyzer_config(self) -> CodeAnalyzerConfig:
        """获取代码分析器配置"""
        analyzer_config = self.config_data.get('code_analyzer', {})
        
        # 创建 CodeAnalyzerConfig 实例
        config = CodeAnalyzerConfig()
        
        # 设置基本参数
        config.root_dir = analyzer_config.get('root_dir')
        config.function_name = analyzer_config.get('function_name')
        config.debug = analyzer_config.get('debug', True)
        config.generlization = analyzer_config.get('generlization', False)
        config.only_loop = analyzer_config.get('only_loop', True)
        config.list_loop = analyzer_config.get('list_loop', False)
        config.auto_annotation = analyzer_config.get('auto_annotation', True)
        config.refine_count = analyzer_config.get('refine_count', 3)
        config.pass_count = analyzer_config.get('pass_count', 5)
        config.think = analyzer_config.get('think', True)
        config.template = analyzer_config.get('template', True)
        config.auto_post = analyzer_config.get('auto_post', True)
        config.use_db = analyzer_config.get('use_db', True)
        config.db_path = analyzer_config.get('db_path', 'VectorDB/Jsons/init.json')
        
        # 设置目录路径
        config.input_dir = analyzer_config.get('input_dir', 'input')
        config.annotated_c_dir = analyzer_config.get('annotated_c_dir', '1_output')
        config.annotated_loop_dir = analyzer_config.get('annotated_loop_dir', '2_output')
        config.generated_loop_dir = analyzer_config.get('generated_loop_dir', '3_output')
        config.output_dir = analyzer_config.get('output_dir', 'output')
        config.log_dir = analyzer_config.get('log_dir', 'log')
        
        return config
    
    def get_llm_config(self) -> LLMConfig:
        """获取LLM配置"""
        llm_config = self.config_data.get('llm', {})
        
        # 创建 LLMConfig 实例
        config = LLMConfig()
        
        # 设置LLM参数
        config.use_api_model = llm_config.get('use_api_model', True)
        config.api_model = llm_config.get('api_model', 'gpt-4o')
        config.api_key = llm_config.get('api_key', '')
        config.base_url = llm_config.get('base_url', 'https://yunwu.ai/v1')
        config.api_temperature = llm_config.get('api_temperature', 0.7)
        config.api_top_p = llm_config.get('api_top_p', 0.7)
        config.think_mode_enabled = llm_config.get('think_mode_enabled', False)
        
        return config
    
    def get_preconditions(self) -> Dict[str, str]:
        """获取前置条件配置"""
        return self.config_data.get('preconditions', {})
    
    def get_model_name(self) -> str:
        """获取模型名称"""
        llm_config = self.config_data.get('llm', {})
        return llm_config.get('api_model', 'gpt-4o')


def load_config_from_file(config_path: str) -> Tuple[CodeAnalyzerConfig, LLMConfig, Dict[str, str], str]:
    """
    从配置文件加载所有配置
    
    Args:
        config_path (str): 配置文件路径
        
    Returns:
        tuple: (CodeAnalyzerConfig, LLMConfig, preconditions, model_name)
    """
    loader = ConfigLoader(config_path)
    
    analyzer_config = loader.get_code_analyzer_config()
    llm_config = loader.get_llm_config()
    preconditions = loader.get_preconditions()
    model_name = loader.get_model_name()
    
    return analyzer_config, llm_config, preconditions, model_name
