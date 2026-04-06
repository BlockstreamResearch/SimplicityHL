#!/usr/bin/env python3
import os
import re
import sys

if len(sys.argv) < 2:
    print("Usage: python3 update_examples.py <new_version>")
    sys.exit(1)

new_version = sys.argv[1]
examples_dir = 'examples'

pattern = r'#!\[compiler_version\("[^"]*"\)\]'
syntax = f'#![compiler_version("{new_version}")]'

for root, _, files in os.walk(examples_dir):
    for file in files:
        if file.endswith('.simf'):
            filepath = os.path.join(root, file)
            with open(filepath, 'r') as f:
                content = f.read()
            
            if re.search(pattern, content):
                updated = re.sub(pattern, syntax, content)
            
            else:
                updated = f"{syntax}\n\n" + content
            
            with open(filepath, 'w') as f:
                f.write(updated)

print(f"Successfully updated all examples to use {syntax}")