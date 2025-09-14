#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
循环不变量Test脚本 - 支持单DatasetTest和不同Model日志分类
"""

import os
import json
from main import MainConfig, FunctionProcessor

def list_files_os(folder_path):
    file_names = []
    for entry in os.listdir(folder_path):
        full_path = os.path.join(folder_path, entry)
        if os.path.isfile(full_path):
            file_names.append(entry)
    return file_names

def get_dataset_config(dataset_name, model_name="default"):
    """获取不同Dataset的配置"""
    configs = {
        'frama-c-loop': {
            'input_dir': './input/frama-c-loop',
            'log_dir': f'./log/frama-c-loop/{model_name}',
            'root_dir': 'frama-c-loop',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'only_loop': False,
                'generlization': False,
                'use_db': False,
                'pass_count': 5
            }
        },
         'frama-c-loop-mask': {
            'input_dir': './input/frama-c-loop-mask',
            'log_dir': f'./log/frama-c-loop-mask/{model_name}',
            'root_dir': 'frama-c-loop-mask',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'only_loop': False,
                'generlization': False,
                'use_db': True,
                'pass_count': 1
            }
        },
         'pIp': {
            'input_dir': './input/pIp',
            'log_dir': f'./log/pIp/{model_name}',
            'root_dir': 'pIp',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'only_loop': False,
                'generlization': False,
                'use_db': True,
                'auto_post': False,
                'pass_count': 5
            }
        },
        'function': {
            'input_dir': './input/function',
            'log_dir': f'./log/function/{model_name}',
            'root_dir': 'function',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'template': True,
                'only_loop': False,
                'generlization': False,
                'use_db': True,
                'refine_count': 3,
                'pass_count': 1,
                'auto_post': True
            }
        },
        'LIG-MM': {
            'input_dir': './input/LIG-MM',
            'log_dir': f'./log/LIG-MM/{model_name}',
            'root_dir': 'LIG-MM',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'only_loop': True,
                'list_loop': True,
                'generlization': False,
                'use_db': True,
                'auto_post': True,
                'pass_count': 5
            }
        },
        'frama-c-hard': {
            'input_dir': './input/frama-c-hard',
            'log_dir': f'./log/frama-c-hard/{model_name}',
            'root_dir': 'frama-c-hard',
            'preconditions': {
            },
            'config_params': {
                'auto_annotation': True,
                'debug': True,
                'only_loop': False,
                'generlization': False,
                'use_db': True,
                'auto_post': True
            }
        }
    }
    
    
    return configs.get(dataset_name, configs['frama-c-loop'])

def test_dataset(dataset_name, model_name="gpt-4o"):
    """Test指定Dataset"""
    config = get_dataset_config(dataset_name, model_name)
    
    name_list = list_files_os(config['input_dir'])
    log_dir = config['log_dir']
    
    # 初始化计数器
    syntax_count = {1: 0, 3: 0, 5: 0}
    valid_count = {1: 0, 3: 0, 5: 0}
    satisfy_count = {1: 0, 3: 0, 5: 0}
    
    count = len(name_list)
    print(f"🔍 Dataset: {dataset_name}")
    print(f"🤖 Model: {model_name}")
    print(f"📁 Input directory: {config['input_dir']}")
    print(f"📊 Found {count} files需要处理")
    print(f"📝 Log directory: {log_dir}")
    
    # 确保Log directory存在
    os.makedirs(log_dir, exist_ok=True)
    
    for name in name_list:
        # 配置参数
        name = name.split('.')[0]
        
        # 根据DatasetType选择日志文件命名格式和函数名
        if dataset_name == 'frama-c-loop' or dataset_name == 'frama-c-loop-mask' or dataset_name == 'function':
            log_path = os.path.join(log_dir, f'goo{name}.log')
            function_name = f'goo{name}'
        elif dataset_name == 'pIp':
            name = name.split('_')[1]
            log_path = os.path.join(log_dir, f'main{name}.log')
            function_name = f'main{name}'
        else:
            log_path = os.path.join(log_dir, f'main{name}.log')
            function_name = f'main{name}'
        
        if os.path.exists(log_path):
            print(f"⏭️ Skip {name}，日志文件already exists")
            continue

        print(f"🔄 Processing file: {name}")

        # 创建配置对象
        config_obj = MainConfig(
            root_dir=config['root_dir'],
            function_name=function_name,
            **config['config_params']
        )

        # 获取预条件字符串，并封装为字典传入处理器
        condition_str = config['preconditions'].get(function_name, 'emp')
        preconditions = {function_name: condition_str}

        try:
            # 执行分析
            processor = FunctionProcessor(config_obj, preconditions, model_name)
            processor.run_analysis()
            first_pass = processor.first_pass

            if first_pass is None:
                print(f"⚠️ {name}: 分析返回 None，SkipStatistics")
                continue
            
            if 'syntax' not in first_pass or 'valid' not in first_pass or 'satisfy' not in first_pass:
                print(f"⚠️ {name}: 分析Result缺少必要的键，SkipStatistics")
                continue
            
            # StatisticsResult
            syntax_score = first_pass['syntax']
            valid_score = first_pass['valid']
            satisfy_score = first_pass['satisfy']
            
            if syntax_score == 1:
                syntax_count[1] += 1
                syntax_count[3] += 1
                syntax_count[5] += 1
            elif syntax_score <= 3:
                syntax_count[3] += 1
                syntax_count[5] += 1
            elif syntax_score <= 5:
                syntax_count[5] += 1
                
            
            if valid_score == 1:
                valid_count[1] += 1
                valid_count[3] += 1
                valid_count[5] += 1
            elif valid_score <= 3:
                valid_count[3] += 1
                valid_count[5] += 1
            elif valid_score <= 5:
                valid_count[5] += 1
            
            if satisfy_score == 1:
                satisfy_count[1] += 1
                satisfy_count[3] += 1
                satisfy_count[5] += 1
            elif satisfy_score <= 3:
                satisfy_count[3] += 1
                satisfy_count[5] += 1
            elif satisfy_score <= 5:
                satisfy_count[5] += 1
            
            print(f"✅ {name}: syntax={syntax_score}, valid={valid_score}, satisfy={satisfy_score}")
            
        except Exception as e:
            print(f"❌ {name}: 处理过程中发生Error: {str(e)}")
            continue

    # OutputStatisticsResult
    print("\n" + "="*60)
    print(f"📊 {dataset_name} DatasetTestResultStatistics (模型: {model_name})")
    print("="*60)
    print(f"Total files: {count}")
    print(f"syntax_count: {syntax_count}")
    print(f"valid_count: {valid_count}")
    print(f"satisfy_count: {satisfy_count}")
    
    if count > 0:
        print(f"\n📈 Pass@1 Statistics:")
        print(f"  syntax_rate: {syntax_count[1]/count:.2%}")
        print(f"  valid_rate: {valid_count[1]/count:.2%}")
        print(f"  satisfy_rate: {satisfy_count[1]/count:.2%}")
        
        print(f"\n📈 Pass@3 Statistics:")
        print(f"  syntax_rate: {syntax_count[3]/count:.2%}")
        print(f"  valid_rate: {valid_count[3]/count:.2%}")
        print(f"  satisfy_rate: {satisfy_count[3]/count:.2%}")
        
        print(f"\n📈 Pass@5 Statistics:")
        print(f"  syntax_rate: {syntax_count[5]/count:.2%}")
        print(f"  valid_rate: {valid_count[5]/count:.2%}")
        print(f"  satisfy_rate: {satisfy_count[5]/count:.2%}")
    
    return {
        'dataset': dataset_name,
        'model': model_name,
        'total_files': count,
        'syntax_count': syntax_count,
        'valid_count': valid_count,
        'satisfy_count': satisfy_count
    }

def main():
    """主函数"""
    print("🚀 函数规约Test脚本启动")
    print("="*60)
    
    # 在这里修改您要Test的Dataset和模型Name
    DATASET_NAME = 'pIp'  # 可选: 'frama-c-loop'
    MODEL_NAME = 'gpt-4o'   # 可选: 'gpt-4o', 'deepseek-V3' 等
    
    print(f"📋 Test配置:")
    print(f"  Dataset: {DATASET_NAME}")
    print(f"  Model: {MODEL_NAME}")
    print(f"  Log directory: ./log/{DATASET_NAME}/{MODEL_NAME}")
    
    # Test指定Dataset
    test_dataset(DATASET_NAME, MODEL_NAME)
    
    print("\n🎉 Test完成！")
    print(f"📊 Results saved to: ./log/{DATASET_NAME}/{MODEL_NAME}/")

if __name__ == '__main__':
    main() 