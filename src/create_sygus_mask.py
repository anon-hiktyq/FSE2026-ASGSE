#!/usr/bin/env python3
import os
import re
import shutil
from pathlib import Path

def remove_assertions_keep_requires(content):
    """
    去掉所有assertion但Keptrequire
    """
    lines = content.split('\n')
    filtered_lines = []
    
    for line in lines:
        stripped = line.strip()
        
        # Keptrequire语句
        if stripped.startswith('/*@ requires') or stripped.startswith('requires'):
            filtered_lines.append(line)
        # 去掉assertion语句
        elif stripped.startswith('/*@ assert') or stripped.startswith('assert'):
            continue
        # Kept其他所有内容
        else:
            filtered_lines.append(line)
    
    return '\n'.join(filtered_lines)

def process_directory():
    """
    处理syGus_code2inv目录，生成syGus_mask目录
    """
    source_dir = Path("/home/yangfp/ARSPG/src/input/syGus_code2inv")
    target_dir = Path("/home/yangfp/ARSPG/src/input/syGus_mask")
    
    # 检查源目录是否存在
    if not source_dir.exists():
        print(f"源Directory does not exist: {source_dir}")
        return
    
    # Create target directory
    target_dir.mkdir(exist_ok=True)
    print(f"Create target directory: {target_dir}")
    
    # 获取所有.c文件
    c_files = list(source_dir.glob("*.c"))
    print(f"Found {len(c_files)} 个C文件")
    
    processed_count = 0
    error_count = 0
    
    for c_file in c_files:
        try:
            # 读取源文件
            with open(c_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 处理内容：去掉assertionKeptrequire
            processed_content = remove_assertions_keep_requires(content)
            
            # 写入目标文件
            target_file = target_dir / c_file.name
            with open(target_file, 'w', encoding='utf-8') as f:
                f.write(processed_content)
            
            processed_count += 1
            print(f"Processing completed: {c_file.name}")
            
        except Exception as e:
            error_count += 1
            print(f"Processing failed {c_file.name}: {e}")
    
    print(f"\nProcessing completed!")
    print(f"Successfully processed: {processed_count} files")
    print(f"Processing failed: {error_count} files")
    print(f"Target directory: {target_dir}")

if __name__ == "__main__":
    process_directory()

