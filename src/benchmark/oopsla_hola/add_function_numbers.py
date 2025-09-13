#!/usr/bin/env python3
"""
Script to add numbers to function names in C files
"""

import os
import re
import glob
from pathlib import Path

def add_function_numbers_to_file(file_path):
    """Add numbers to function names in a single C file"""
    print(f"Processing {file_path}...")
    
    # Read the file content
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract file number from filename (e.g., "01.c" -> "01")
    file_number = Path(file_path).stem
    
    # Find all function definitions and declarations
    # Pattern to match function definitions: return_type function_name(parameters)
    function_pattern = r'(\w+)\s+(\w+)\s*\([^)]*\)\s*\{'
    
    # Pattern to match function declarations: return_type function_name(parameters);
    declaration_pattern = r'(\w+)\s+(\w+)\s*\([^)]*\)\s*;'
    
    # Pattern to match function calls: function_name(
    call_pattern = r'(\b\w+)\s*\('
    
    # Get all function names from definitions
    function_matches = re.findall(function_pattern, content)
    function_names = [match[1] for match in function_matches]
    
    # Get all function names from declarations
    declaration_matches = re.findall(declaration_pattern, content)
    declaration_names = [match[1] for match in declaration_matches]
    
    # Combine all function names
    all_function_names = list(set(function_names + declaration_names))
    
    # Filter out common C keywords and library functions
    exclude_keywords = {
        'if', 'for', 'while', 'switch', 'return', 'sizeof', 'malloc', 'free',
        'printf', 'scanf', 'unknown', 'main', 'assert', 'requires', 'ensures'
    }
    
    function_names = [name for name in all_function_names if name not in exclude_keywords]
    
    print(f"  Found functions: {function_names}")
    
    # Create a mapping of old names to new names
    name_mapping = {}
    for i, name in enumerate(function_names, 1):
        new_name = f"{name}{file_number}"
        name_mapping[name] = new_name
        print(f"  {name} -> {new_name}")
    
    # Replace function definitions
    for old_name, new_name in name_mapping.items():
        # Replace function definitions
        content = re.sub(
            rf'(\w+)\s+{re.escape(old_name)}\s*\(([^)]*)\)\s*{{',
            rf'\1 {new_name}(\2) {{',
            content
        )
        
        # Replace function declarations
        content = re.sub(
            rf'(\w+)\s+{re.escape(old_name)}\s*\(([^)]*)\)\s*;',
            rf'\1 {new_name}(\2);',
            content
        )
        
        # Replace function calls (but be careful not to replace too much)
        # Only replace if it's followed by an opening parenthesis and not already replaced
        content = re.sub(
            rf'\b{re.escape(old_name)}\s*\(',
            rf'{new_name}(',
            content
        )
    
    # Write the modified content back to the file
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"  ✓ Updated {file_path}")

def main():
    """Main function to process all C files in the current directory"""
    # Get all .c files in the current directory
    c_files = glob.glob("*.c")
    
    if not c_files:
        print("No .c files found in current directory")
        return
    
    print(f"Found {len(c_files)} C files to process")
    print("=" * 50)
    
    # Process each file
    for c_file in sorted(c_files):
        try:
            add_function_numbers_to_file(c_file)
        except Exception as e:
            print(f"Error processing {c_file}: {e}")
    
    print("=" * 50)
    print("All files processed!")

if __name__ == "__main__":
    main() 