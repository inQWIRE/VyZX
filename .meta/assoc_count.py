#!/usr/bin/env python3

import re
import os
import sys
import functools 
import argparse


MIN_PYTHON = (3, 10)
if sys.version_info < MIN_PYTHON:
  print(f"Your python version is {sys.version_info.major}.{sys.version_info.minor}. {MIN_PYTHON[0]}.{MIN_PYTHON[1]} is required")
  exit(3)

b_color_yellow = '\033[93m'
b_color_cyan = '\033[96m'
b_color_reset = '\033[0m'
b_color_green = '\033[92m'
b_color_red = '\033[91m'

b_color_yellow = ''
b_color_cyan = ''
b_color_reset = ''
b_color_green = ''
b_color_red = ''

is_windows = sys.platform.startswith('win')
if is_windows: # Disable colors on windows 
  b_color_yellow = ''
  b_color_cyan = ''
  b_color_reset = ''
  b_color_green = ''
  b_color_red = ''
  print("Warning: Windows detected. Disabling colored output")
  
curr_dir = os.path.dirname(os.path.realpath(__file__))
src_dir = f"{curr_dir}/../src"

regex_assoc : list[re.Pattern] = list(map(re.compile, [
  r".*rewrite.*assoc",
  r".*rewrite.*dist",
  r".*rewrite.*mixed_product",
  r".*rewrite.*cast",
  r".*cleanup_zx",
  r".*cast_id",
  r".*simpl_cast",
  r".*bundle_wires",
  r".*restore_dims",
  r".*cast_irrelevance",
  r".*apply .*_simplify",
  r".*rewrite.*stack_empty_.",
  r".*rewrite.*n_stack1_",
  r".*rewrite.*n_wire_stack",
  r".*rewrite.*wire_to_n_wire",
  r".*rewrite.*wire_removal_",
  r".*rewrite.*(n_wire|nstack1)_split",
]))
lemma_theorem_regex = re.compile(r'(?:Lemma|Theorem)\s+(\w+)\s*:(?:[\s\S]*?)Proof\.\s*([\s\S]*?)(Qed\.|Admitted\.|Defined\.|Abort\.)')
proof_regex = re.compile(r'Proof\.((?:(?!Proof\.|Qed\.|Defined\.|Admitted\.|Abort\.)(?!\b(?:Proof|Qed|Defined|Admitted|Abort)\b)[\s\S])*?)(Qed\.|Defined\.|Admitted\.|Abort\.)')
stmt_regex = re.compile(r'(([a-z|A-Z|0-9])+(\t| |[a-z|A-Z|0-9]|.)*)(\t| )*(\n|;|$)')

class Result:
  nam : str
  non_assoc : int
  assoc : int
  repeat_assoc : int

  def __init__(self, nam : str = "", non_assoc : int = 0, assoc : int = 0, repeat_assoc : int = 0) -> None:
    self.nam = nam
    self.non_assoc = non_assoc  
    self.assoc = assoc
    self.repeat_assoc = repeat_assoc
  
  
  def __add__(self, other):
    return Result(self.non_assoc + other.non_assoc, self.assoc + other.assoc, self.repeat_assoc + other.repeat_assoc)
  
  def __iadd__(self, other):
    self.assoc += other.assoc
    self.non_assoc += other.non_assoc
    self.repeat_assoc += other.repeat_assoc
    return self
  
  def total_assoc(self) -> int:
    return self.assoc + self.repeat_assoc
  
  def total(self) -> int:
    return self.total_assoc() + self.non_assoc
    
  def __str__(self) -> str:
    # if self.nam != "":
        return \
f"| {self.nam} | {self.repeat_assoc} ({self.repeat_assoc / self.total():.0%}) | {self.assoc}  ({self.assoc / self.total():.0%}) | {self.total_assoc()} ({self.total_assoc() / self.total():.0%}) | {b_color_reset} {self.non_assoc} ({self.non_assoc / self.total():.0%}) | {self.total()} |"
# f"""In proof {self.nam}:
# {b_color_red}Number of repeated assoc lines:{b_color_reset} {self.repeat_assoc} ({self.repeat_assoc / self.total():.2%})
# {b_color_yellow}Number of assoc lines:{b_color_reset} {self.assoc}  ({self.assoc / self.total():.2%})
# {b_color_cyan}Total of any assoc lines:{b_color_reset} {self.total_assoc()} ({self.total_assoc() / self.total():.2%})
# {b_color_green}Number of other proof lines:{b_color_reset} {self.non_assoc} ({self.non_assoc / self.total():.2%})
# Total lines: {self.total()}
# """
#     else:
#         return \
# f"""{b_color_red}Number of repeated assoc lines:{b_color_reset} {self.repeat_assoc} ({self.repeat_assoc / self.total():.2%}) ({self.repeat_assoc / self.total_assoc():.2%} of all assoc lines)
# {b_color_yellow}Number of assoc lines:{b_color_reset} {self.assoc} ({self.assoc / self.total():.2%}) ({self.assoc / self.total_assoc():.2%} of all assoc lines)
# {b_color_cyan}Total of any assoc lines:{b_color_reset} {self.total_assoc()} ({self.total_assoc() / self.total():.2%})
# {b_color_green}Number of other proof lines:{b_color_reset} {self.non_assoc} ({self.non_assoc / self.total():.2%})
# Total lines: {self.total()}
# """
    
do_regex = re.compile(r'do \d+')
  

def count_assoc_non_assoc(proof : str, proof_completion : str) -> Result:
  if proof_completion != "Qed." and proof_completion != "Defined.":
    return Result()
  result = Result()
  for stmt in stmt_regex.findall(proof):
    if any(map(lambda pattern : pattern.match(stmt[0]), regex_assoc)):
      if 'repeat' in stmt[0] or do_regex.match(stmt[0]):
        result.repeat_assoc += 1
      else:
        result.assoc += 1
    else:
      result.non_assoc += 1
  return result

def count_assoc_non_assoc_named(n : str, proof : str, proof_completion : str) -> Result:
  if proof_completion != "Qed." and proof_completion != "Defined.":
    return Result()
  result = Result()
  result.nam = n
  for stmt in stmt_regex.findall(proof):
    if any(map(lambda pattern : pattern.match(stmt[0]), regex_assoc)):
      if 'repeat' in stmt[0] or do_regex.match(stmt[0]):
        result.repeat_assoc += 1
      else:
        result.assoc += 1
    else:
      result.non_assoc += 1
  return result

def count_assoc_by_proof_file (file : str) -> list[Result]:
    with open(file) as f:
        data=f.read()
        proofs=lemma_theorem_regex.findall(data)
        return [count_assoc_non_assoc_named(proof[0],proof[1], proof[2]) for proof in proofs]

def count_assoc_file(file : str) -> Result:
  with open(file) as f:
    data = f.read()
    proofs = proof_regex.findall(data)
    result = functools.reduce(lambda curr, proof : count_assoc_non_assoc(proof[0], proof[-1]) + curr , proofs, Result())
    return result
  
parser = argparse.ArgumentParser(
                  prog='assoc_count',
                  description='Counts assoc lines')
parser.add_argument('-f','--file', type=str, help='Optional filename to process signle file')
parser.add_argument('-p','--proof', action='store_true')

args = parser.parse_args()

results = []
if args.file:
    if args.proof:
        file = args.file
        if not file.endswith(".v"): # Make sure we only look at Coq files
            print(f"{b_color_red}Error: file provided is not a Coq file. Doing nothing")
            exit(2) 
        results = count_assoc_by_proof_file(file)
    else:
        file = args.file
        if not file.endswith(".v"): # Make sure we only look at Coq files
            print(f"{b_color_red}Error: file provided is not a Coq file. Doing nothing")
            exit(2) 
        results.append(count_assoc_file(file))
elif args.proof:
    for dir, _, files in os.walk(src_dir):
        for file in files:
            # print(f"Checking {dir}/{file}...")
            if not file.endswith(".v"): # Make sure we only look at Coq files
              continue
            results += count_assoc_by_proof_file(f"{dir}/{file}")
else:
    results.append(Result())
    for dir, _, files in os.walk(src_dir):
        for file in files:
            # print(f"Checking {dir}/{file}...")
            if not file.endswith(".v"): # Make sure we only look at Coq files
                continue
            results[0] += count_assoc_file(f"{dir}/{file}")
    
print("| Proof Name | Repeated Assoc Lines (%) | Assoc Lines (%) | Total Assoc Lines (%) | Other Proof Lines (%) | Total Lines |")
print("| :-- | :--: | :--: | :--: | :--: | :--: |")
for result in results:
    if result.total() >= 20 and result.total_assoc() > 0:
        print(result)
