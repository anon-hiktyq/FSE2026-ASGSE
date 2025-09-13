#!/usr/bin/env python3
import os
import subprocess
import re
import time
import glob
from pathlib import Path

def run_fuzz_command(file_path, attempt_num, timeout=50):
    """
    运行fuzz.py命令
    返回: (success, output_dir)
    """
    print(f"运行命令: timeout {timeout}s ./fuzz.py -f {file_path} -m gpt-4o")
    
    try:
        result = subprocess.run(
            f"timeout {timeout}s ./fuzz.py -f {file_path} -m gpt-4o",
            shell=True,
            capture_output=True,
            text=True,
            timeout=timeout + 10
        )
        
        # 检查输出目录，第n次尝试对应 _000n
        file_name = Path(file_path).stem
        output_dir = f"out/{file_name}_{attempt_num:04d}"
        
        if os.path.exists(output_dir):
            print(f"✓ 成功生成输出目录: {output_dir}")
            return True, output_dir
        
        print(f"✗ 未找到输出目录: {output_dir}")
        return False, None
        
    except subprocess.TimeoutExpired:
        print(f"✗ 命令超时 ({timeout}s)")
        return False, None
    except Exception as e:
        print(f"✗ 命令执行失败: {e}")
        return False, None

def get_latest_txt_file(output_dir):
    """
    获取输出目录中最新的txt文件（按文件名排序，取最后一个）
    """
    if not os.path.exists(output_dir):
        return None
    
    # 查找所有txt文件
    txt_files = list(Path(output_dir).glob("*.txt"))
    
    if not txt_files:
        return None
    
    # 按文件名排序，返回最后一个（通常是编号最大的）
    txt_files.sort()
    latest_file = txt_files[-1]
    return str(latest_file)

def read_final_result_file(output_dir):
    """
    读取 output_dir 下的 final_result 并判断是否包含 Pass。
    返回: (found_final_result: bool, is_pass: Optional[bool])
    """
    final_path = os.path.join(output_dir, "final_result")
    if not os.path.exists(final_path):
        return False, None
    try:
        with open(final_path, 'r', encoding='utf-8') as f:
            content = f.read()
        return True, ("Pass" in content)
    except Exception:
        # 找到但读取失败，当作找到但未知结果
        return True, None

def analyze_verification_goals(txt_file):
    """
    分析验证结果文件，检查关键目标是否满足
    要求：Loop Invariant、Assertion、Post-condition都需要正确，但只有Assertion不能为空
    返回: (all_satisfied, details)
    """
    if not os.path.exists(txt_file):
        print(f"✗ 文件不存在: {txt_file}")
        return False, {"error": "文件不存在"}
    
    try:
        with open(txt_file, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"✗ 读取文件失败: {e}")
        return False, {"error": str(e)}
    
    # 定义需要检查的目标类型
    required_goals = [
        "Preservation of Invariant",
        "Establishment of Invariant", 
        "Assertion",
        "Post-condition"
    ]
    
    goal_results = {}
    all_satisfied = True
    found_any_goals = False  # 是否找到任何目标
    has_assertion = False  # 是否有assertion
    
    # 分析每个目标类型
    for goal_type in required_goals:
        goal_results[goal_type] = {
            "total": 0,
            "valid": 0,
            "invalid": 0,
            "timeout": 0,
            "failed": 0
        }
        
        # 查找该目标类型的所有实例
        pattern = rf'Goal\s+{re.escape(goal_type)}[^:]*:.*?Prover\s+[^:]+returns\s+(\w+)'
        matches = re.findall(pattern, content, re.DOTALL | re.IGNORECASE)
        
        for result in matches:
            goal_results[goal_type]["total"] += 1
            found_any_goals = True
            
            # 检查是否有assertion
            if goal_type == "Assertion":
                has_assertion = True
            
            if result.strip().lower() == "valid":
                goal_results[goal_type]["valid"] += 1
            elif result.strip().lower() == "timeout":
                goal_results[goal_type]["timeout"] += 1
            elif result.strip().lower() in ["invalid", "failed"]:
                goal_results[goal_type]["invalid"] += 1
            else:
                goal_results[goal_type]["failed"] += 1
    
    # 新的判断逻辑：
    # 1. Assertion必须存在且不能为空
    if not has_assertion or goal_results["Assertion"]["total"] == 0:
        print(f"    ✗ Assertion必须存在且不能为空")
        all_satisfied = False
    
    # 2. 对于Loop Invariant和Post-condition，如果存在则必须全部正确
    loop_invariant_types = ["Preservation of Invariant", "Establishment of Invariant"]
    for goal_type in loop_invariant_types:
        if goal_results[goal_type]["total"] > 0:
            if goal_results[goal_type]["invalid"] > 0 or goal_results[goal_type]["timeout"] > 0:
                print(f"    ✗ {goal_type}存在但未全部通过")
                all_satisfied = False
    
    # 3. Post-condition如果存在则必须全部正确
    if goal_results["Post-condition"]["total"] > 0:
        if goal_results["Post-condition"]["invalid"] > 0 or goal_results["Post-condition"]["timeout"] > 0:
            print(f"    ✗ Post-condition存在但未全部通过")
            all_satisfied = False
    
    # 4. Assertion如果存在则必须全部正确
    if goal_results["Assertion"]["total"] > 0:
        if goal_results["Assertion"]["invalid"] > 0 or goal_results["Assertion"]["timeout"] > 0:
            print(f"    ✗ Assertion存在但未全部通过")
            all_satisfied = False
    
    # 打印分析结果
    print(f"  目标分析结果:")
    for goal_type in required_goals:
        stats = goal_results[goal_type]
        if stats["total"] > 0:
            status = "✓" if stats["invalid"] == 0 and stats["timeout"] == 0 else "✗"
            print(f"    {status} {goal_type}: {stats['valid']}/{stats['total']} 通过")
            if stats["invalid"] > 0:
                print(f"      ✗ 失败: {stats['invalid']}")
            if stats["timeout"] > 0:
                print(f"      ⏰ 超时: {stats['timeout']}")
        else:
            print(f"    - {goal_type}: 未找到")
    
    if not found_any_goals:
        print(f"    ⚠ 警告: 未找到任何目标")
    
    return all_satisfied, goal_results

def process_file_pass5(file_path, max_attempts=5, timeout=50):
    """
    对单个文件执行pass@5处理
    返回: (success, attempts, best_result)
    """
    print(f"\n{'='*60}")
    print(f"开始处理文件: {file_path}")
    print(f"最大尝试次数: {max_attempts}")
    print(f"{'='*60}")
    
    file_name = Path(file_path).stem
    pickle_file = f"{file_path}.pickle"
    
    best_result = None
    successful_attempts = 0
    
    for attempt in range(1, max_attempts + 1):
        print(f"\n--- 第 {attempt}/{max_attempts} 次尝试 ---")
        
        # 删除pickle文件以确保重新运行
        if os.path.exists(pickle_file):
            os.remove(pickle_file)
            print(f"删除了pickle文件: {pickle_file}")
        
        # 运行fuzz命令
        success, output_dir = run_fuzz_command(file_path, attempt, timeout)
        
        if not success:
            print(f"✗ 第 {attempt} 次尝试失败")
            continue
        
        # 仅以 final_result 为准（或超时）判定本次尝试是否结束；若 final_result 含 Pass 则该文件成功并进入下一个文件
        found_final, is_pass = read_final_result_file(output_dir)
        if not found_final:
            print(f"✗ 第 {attempt} 次尝试：未找到 final_result")
            continue
        print(f"✓ 找到 final_result: {os.path.join(output_dir, 'final_result')}")
        if is_pass is True:
            print(f"✓ 第 {attempt} 次尝试：final_result 显示 Pass，进入下一个文件")
            successful_attempts += 1
            best_result = {
                "attempt": attempt,
                "output_dir": output_dir,
                "txt_file": os.path.join(output_dir, 'final_result'),
                "details": {"final_result": "Pass"}
            }
            break
        elif is_pass is False:
            print(f"✗ 第 {attempt} 次尝试：final_result 非 Pass")
            continue
        else:
            print(f"⚠ 第 {attempt} 次尝试：final_result 读取失败或无法解析")
            continue
    
    # 输出最终结果
    print(f"\n{'='*60}")
    print(f"文件 {file_name} 处理完成")
    print(f"{'='*60}")
    print(f"总尝试次数: {max_attempts}")
    print(f"成功次数: {successful_attempts}")
    
    if best_result:
        print(f"✓ 最佳结果: 第 {best_result['attempt']} 次尝试")
        print(f"  输出目录: {best_result['output_dir']}")
        print(f"  验证文件: {best_result['txt_file']}")
        return True, max_attempts, best_result
    else:
        print(f"✗ 所有尝试都失败")
        return False, max_attempts, None

def batch_process_files(start_file=19, end_file=133, max_attempts=5, timeout=50):
    """
    批量处理文件
    """
    print("AutoSpec Pass@5 批量验证脚本")
    print("="*60)
    print(f"处理文件范围: {start_file}-{end_file}")
    print(f"每个文件最多尝试: {max_attempts} 次")
    print(f"单次超时: {timeout} 秒")
    print("="*60)
    
    results = []
    successful_files = 0
    failed_files = 0
    total_attempts = 0
    processed_files = 0
    
    for i in range(start_file, end_file + 1):
        file_path = f"benchmark/pIp/{i}.c"
        
        if not os.path.exists(file_path):
            print(f"✗ 文件不存在: {file_path}")
            continue
        
        processed_files += 1
        
        # 处理文件
        success, attempts, best_result = process_file_pass5(file_path, max_attempts, timeout)
        
        result = {
            "file": file_path,
            "file_number": i,
            "success": success,
            "attempts": attempts,
            "best_result": best_result
        }
        results.append(result)
        
        total_attempts += attempts
        
        if success:
            successful_files += 1
            print(f"✓ 文件 {i}.c: 成功")
        else:
            failed_files += 1
            print(f"✗ 文件 {i}.c: 失败")
        
        print(f"进度: {processed_files}/{end_file-start_file+1}")
        print("-" * 40)
    
    # 计算正确率
    accuracy_rate = successful_files / processed_files if processed_files > 0 else 0
    
    # 输出统计结果
    print(f"\n{'='*60}")
    print("批量处理结果统计:")
    print(f"{'='*60}")
    print(f"总文件数: {processed_files}")
    print(f"成功文件数: {successful_files}")
    print(f"失败文件数: {failed_files}")
    print(f"总尝试次数: {total_attempts}")
    print(f"正确率: {successful_files}/{processed_files} = {accuracy_rate*100:.1f}%")
    
    # 保存统计结果到文件
    save_results_to_file(results, successful_files, processed_files, accuracy_rate, start_file, end_file)
    
    return results

def save_results_to_file(results, successful_files, total_files, accuracy_rate, start_file, end_file):
    """
    保存结果到文件
    """
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    filename = f"pass5_results_{start_file}_{end_file}_{timestamp}.txt"
    
    with open(filename, 'w', encoding='utf-8') as f:
        f.write("AutoSpec Pass@5 验证结果报告\n")
        f.write("="*60 + "\n")
        f.write(f"生成时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"处理文件范围: {start_file}-{end_file}\n")
        f.write(f"总文件数: {total_files}\n")
        f.write(f"成功文件数: {successful_files}\n")
        f.write(f"失败文件数: {total_files - successful_files}\n")
        f.write(f"正确率: {successful_files}/{total_files} = {accuracy_rate*100:.1f}%\n")
        f.write("\n")
        
        f.write("详细结果:\n")
        f.write("-" * 40 + "\n")
        for result in results:
            status = "✓" if result["success"] else "✗"
            f.write(f"{status} {result['file_number']}.c")
            if result["success"] and result["best_result"]:
                f.write(f" (第{result['best_result']['attempt']}次尝试成功)")
            f.write("\n")
        
        f.write("\n")
        f.write("统计摘要:\n")
        f.write("-" * 40 + "\n")
        f.write(f"正确率: {successful_files}/{total_files} = {accuracy_rate*100:.1f}%\n")
        
        # 按成功次数统计
        success_by_attempt = {}
        for result in results:
            if result["success"] and result["best_result"]:
                attempt = result["best_result"]["attempt"]
                success_by_attempt[attempt] = success_by_attempt.get(attempt, 0) + 1
        
        if success_by_attempt:
            f.write("\n成功尝试分布:\n")
            for attempt in sorted(success_by_attempt.keys()):
                f.write(f"  第{attempt}次尝试成功: {success_by_attempt[attempt]} 个文件\n")
    
    print(f"\n结果已保存到文件: {filename}")
    
    # 同时保存简化的正确率文件
    accuracy_filename = f"accuracy_rate_{start_file}_{end_file}.txt"
    with open(accuracy_filename, 'w', encoding='utf-8') as f:
        f.write(f"{successful_files}/{total_files}\n")
        f.write(f"{accuracy_rate*100:.1f}%\n")
    
    print(f"正确率已保存到文件: {accuracy_filename}")

def main():
    """
    主函数
    """
    import sys
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "batch":
            # 批量处理模式
            start_file = int(sys.argv[2]) if len(sys.argv) > 2 else 1
            end_file = int(sys.argv[3]) if len(sys.argv) > 3 else 133
            max_attempts = int(sys.argv[4]) if len(sys.argv) > 4 else 5
            timeout = int(sys.argv[5]) if len(sys.argv) > 5 else 50
            
            batch_process_files(start_file, end_file, max_attempts, timeout)
        else:
            # 单文件模式
            file_path = sys.argv[1]
            max_attempts = int(sys.argv[2]) if len(sys.argv) > 2 else 5
            timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 50
            
            if not os.path.exists(file_path):
                print(f"✗ 文件不存在: {file_path}")
                return
            
            success, attempts, best_result = process_file_pass5(file_path, max_attempts, timeout)
            
            print(f"\n{'='*60}")
            print("最终结果:")
            print(f"{'='*60}")
            print(f"文件: {file_path}")
            print(f"成功: {'✓ 是' if success else '✗ 否'}")
            print(f"尝试次数: {attempts}")
            if best_result:
                print(f"最佳结果: 第 {best_result['attempt']} 次尝试")
    else:
        print("使用方法:")
        print("  单文件: python3 pass5_verification.py <file_path> [max_attempts] [timeout]")
        print("  批量:   python3 pass5_verification.py batch [start] [end] [max_attempts] [timeout]")
        print("  示例:   python3 pass5_verification.py benchmark/syGus_code2inv/1.c 5 50")
        print("  示例:   python3 pass5_verification.py batch 1 133 5 50")

if __name__ == "__main__":
    main()
